#!/usr/bin/env python3
from __future__ import annotations

import argparse
import hashlib
import itertools
import json
import os
import platform as py_platform
import re
import subprocess
import sys
from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

SCRIPT_DIR = Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

from validate_sat_witness import validate_witness  # noqa: E402

DECODE_MODEL = SCRIPT_DIR / "decode_model.py"
GALLERY_SCHEMA_VERSION = 1
DEFAULT_THRESHOLDS: dict[str, float] = {
    "min_distinct_social_outcomes": 2.0,
    "max_dictatorship_score_max": 0.95,
    "max_constant_function_rate": 0.999999,
}


@dataclass
class Candidate:
    case_id: str
    case: dict[str, Any]
    case_dir: Path
    metrics: dict[str, Any]
    model_validated: bool
    validator_stats: dict[str, Any]
    non_trivial: bool
    nontriviality_report: dict[str, Any]
    rule_path: Path | None
    rule_card_md_path: Path | None
    rule_card_tex_path: Path | None
    model_path: Path | None
    cnf_path: Path
    manifest_path: Path


def _load_json(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


def _write_json(path: Path, payload: dict[str, Any]) -> None:
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def _sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def _probe_git_commit() -> str:
    try:
        proc = subprocess.run(
            ["git", "rev-parse", "HEAD"],
            cwd=SCRIPT_DIR.parent,
            capture_output=True,
            text=True,
            check=False,
            timeout=5.0,
        )
    except (FileNotFoundError, subprocess.TimeoutExpired):
        return "unknown"
    if proc.returncode != 0:
        return "unknown"
    commit = proc.stdout.strip()
    return commit if commit else "unknown"


def _sanitize_path_string(value: Any) -> str:
    text = str(value).strip() if value is not None else ""
    if not text or text == "unknown":
        return "unknown"
    if re.match(r"^[A-Za-z]:\\", text):
        return "<absolute>/" + Path(text).name
    path = Path(text)
    if path.is_absolute():
        return "<absolute>/" + path.name
    return text


def _normalize_cases(atlas: dict[str, Any]) -> list[dict[str, Any]]:
    raw = atlas.get("cases", [])
    if isinstance(raw, list):
        return [c for c in raw if isinstance(c, dict)]
    if isinstance(raw, dict):
        return [c for c in raw.values() if isinstance(c, dict)]
    return []


def _compute_metrics(model_path: Path, manifest_path: Path) -> dict[str, Any]:
    model = _load_json(model_path)
    manifest = _load_json(manifest_path)

    nprofiles = int(manifest["nprofiles"])
    npairs = int(manifest["npairs"])
    nranks = int(manifest["nranks"])
    pair_order = [tuple(x) for x in manifest["pair_order"]]

    rankings = list(itertools.permutations([0, 1, 2, 3], 4))
    if len(rankings) != nranks:
        raise ValueError(f"ranking count mismatch: expected {nranks}, got {len(rankings)}")
    pos_maps = [{a: i for i, a in enumerate(r)} for r in rankings]

    n_p_vars = int(manifest["n_p_vars"])
    true_vars = {int(v) for v in model.get("true_vars", []) if 1 <= int(v) <= n_p_vars}

    total_atoms = nprofiles * npairs
    match_counts = [0, 0]
    pair_support = [0 for _ in range(npairs)]
    signatures: set[tuple[int, ...]] = set()

    for p in range(nprofiles):
        r0_idx = p // nranks
        r1_idx = p % nranks
        pos0 = pos_maps[r0_idx]
        pos1 = pos_maps[r1_idx]
        sig_bits: list[int] = []

        for pair_idx, (a, b) in enumerate(pair_order):
            var = 1 + p * npairs + pair_idx
            social = var in true_vars
            if social:
                pair_support[pair_idx] += 1

            pref0 = pos0[a] < pos0[b]
            pref1 = pos1[a] < pos1[b]
            if social == pref0:
                match_counts[0] += 1
            if social == pref1:
                match_counts[1] += 1
            sig_bits.append(1 if social else 0)

        signatures.add(tuple(sig_bits))

    dictatorship0 = (match_counts[0] / total_atoms) if total_atoms > 0 else 0.0
    dictatorship1 = (match_counts[1] / total_atoms) if total_atoms > 0 else 0.0
    dictatorship_max = max(dictatorship0, dictatorship1)

    support_mode = max(pair_support) if pair_support else 0
    neutrality_violation_count = sum(1 for count in pair_support if count != support_mode)
    distinct_social_outcomes = len(signatures)
    constant_function_rate = 1.0 if distinct_social_outcomes == 1 else 0.0

    return {
        "dictatorship_score_voter0": float(dictatorship0),
        "dictatorship_score_voter1": float(dictatorship1),
        "dictatorship_score_max": float(dictatorship_max),
        "neutrality_violation_count": int(neutrality_violation_count),
        "distinct_social_outcomes": int(distinct_social_outcomes),
        "constant_function_rate": float(constant_function_rate),
    }


def _build_nontriviality_report(metrics: dict[str, Any], thresholds: dict[str, float]) -> dict[str, Any]:
    distinct = float(metrics.get("distinct_social_outcomes", 0.0))
    dictatorship_max = float(metrics.get("dictatorship_score_max", 1.0))
    constant_rate = float(metrics.get("constant_function_rate", 1.0))

    excluded_reasons: list[str] = []
    if distinct < float(thresholds["min_distinct_social_outcomes"]):
        excluded_reasons.append("distinct_social_outcomes_below_threshold")
    if dictatorship_max > float(thresholds["max_dictatorship_score_max"]):
        excluded_reasons.append("dictatorship_score_max_above_threshold")
    if constant_rate > float(thresholds["max_constant_function_rate"]):
        excluded_reasons.append("constant_function_rate_above_threshold")

    included_reasons = ["passes_non_triviality_thresholds"] if not excluded_reasons else []
    return {
        "passes_non_triviality": len(excluded_reasons) == 0,
        "included_reasons": included_reasons,
        "excluded_reasons": excluded_reasons,
        "thresholds": {
            "min_distinct_social_outcomes": float(thresholds["min_distinct_social_outcomes"]),
            "max_dictatorship_score_max": float(thresholds["max_dictatorship_score_max"]),
            "max_constant_function_rate": float(thresholds["max_constant_function_rate"]),
        },
    }


def _fmt_perm(perm: tuple[int, ...]) -> str:
    return "[" + ",".join(str(x) for x in perm) + "]"


def _tex_escape(text: str) -> str:
    out = text
    replacements = {
        "\\": r"\textbackslash{}",
        "&": r"\&",
        "%": r"\%",
        "$": r"\$",
        "#": r"\#",
        "_": r"\_",
        "{": r"\{",
        "}": r"\}",
        "~": r"\textasciitilde{}",
        "^": r"\textasciicircum{}",
    }
    for src, dst in replacements.items():
        out = out.replace(src, dst)
    return out


def _build_rule_witnesses(
    *,
    model_path: Path,
    manifest_path: Path,
    max_witnesses: int = 3,
) -> list[dict[str, Any]]:
    model = _load_json(model_path)
    manifest = _load_json(manifest_path)
    nprofiles = int(manifest["nprofiles"])
    npairs = int(manifest["npairs"])
    nranks = int(manifest["nranks"])
    pair_order = [tuple(x) for x in manifest["pair_order"]]
    n_p_vars = int(manifest["n_p_vars"])

    rankings = list(itertools.permutations([0, 1, 2, 3], 4))
    if len(rankings) != nranks:
        raise ValueError(f"ranking count mismatch: expected {nranks}, got {len(rankings)}")
    pos_maps = [{a: i for i, a in enumerate(r)} for r in rankings]

    true_vars = {int(v) for v in model.get("true_vars", []) if 1 <= int(v) <= n_p_vars}

    def social_bit(profile_idx: int, pair_idx: int) -> int:
        var = 1 + profile_idx * npairs + pair_idx
        return 1 if var in true_vars else 0

    profile_rows: list[dict[str, Any]] = []
    sig_to_profile: dict[tuple[int, ...], int] = {}
    nonconstant_pair: tuple[int, int] | None = None
    mismatch_v0: int | None = None
    mismatch_v1: int | None = None

    for p in range(nprofiles):
        r0_idx = p // nranks
        r1_idx = p % nranks
        r0 = rankings[r0_idx]
        r1 = rankings[r1_idx]
        pos0 = pos_maps[r0_idx]
        pos1 = pos_maps[r1_idx]
        social_bits = [social_bit(p, i) for i in range(npairs)]

        pref0_bits = [1 if pos0[a] < pos0[b] else 0 for (a, b) in pair_order]
        pref1_bits = [1 if pos1[a] < pos1[b] else 0 for (a, b) in pair_order]
        differs_v0 = any(s != v for s, v in zip(social_bits, pref0_bits))
        differs_v1 = any(s != v for s, v in zip(social_bits, pref1_bits))
        edges = [f"{a}>{b}" for i, (a, b) in enumerate(pair_order) if social_bits[i] == 1]

        signature = tuple(social_bits)
        if signature not in sig_to_profile:
            sig_to_profile[signature] = p
            if len(sig_to_profile) >= 2 and nonconstant_pair is None:
                first_sig, second_sig = list(sig_to_profile.values())[:2]
                nonconstant_pair = (first_sig, second_sig)
        if mismatch_v0 is None and differs_v0:
            mismatch_v0 = p
        if mismatch_v1 is None and differs_v1:
            mismatch_v1 = p

        profile_rows.append(
            {
                "profile_id": p,
                "r0": r0,
                "r1": r1,
                "edges": edges,
                "differs_v0": differs_v0,
                "differs_v1": differs_v1,
            }
        )

    selected_profile_ids: list[int] = []
    if nonconstant_pair is not None:
        selected_profile_ids.extend([nonconstant_pair[0], nonconstant_pair[1]])
    if mismatch_v0 is not None:
        selected_profile_ids.append(mismatch_v0)
    if mismatch_v1 is not None:
        selected_profile_ids.append(mismatch_v1)

    deduped_ids: list[int] = []
    seen: set[int] = set()
    for pid in selected_profile_ids:
        if pid in seen:
            continue
        seen.add(pid)
        deduped_ids.append(pid)
        if len(deduped_ids) >= max_witnesses:
            break

    if not deduped_ids:
        deduped_ids = [0]

    witnesses: list[dict[str, Any]] = []
    profile_lookup = {int(row["profile_id"]): row for row in profile_rows}
    for pid in deduped_ids:
        row = profile_lookup[pid]
        witness_tags: list[str] = []
        if nonconstant_pair is not None and pid in nonconstant_pair:
            witness_tags.append("non_constant_witness")
        if row["differs_v0"]:
            witness_tags.append("non_dictatorship_voter0_witness")
        if row["differs_v1"]:
            witness_tags.append("non_dictatorship_voter1_witness")
        if not witness_tags:
            witness_tags.append("fallback_sample")

        witnesses.append(
            {
                "profile_id": int(row["profile_id"]),
                "r0": list(row["r0"]),
                "r1": list(row["r1"]),
                "social_edges": list(row["edges"]),
                "differs_from_voter0": bool(row["differs_v0"]),
                "differs_from_voter1": bool(row["differs_v1"]),
                "witness_tags": witness_tags,
            }
        )

    return witnesses


def _write_rule_cards(
    *,
    case_id: str,
    case_dir: Path,
    axioms_on: list[str],
    metrics: dict[str, Any],
    nontriviality_report: dict[str, Any],
    model_validated: bool,
    manifest_path: Path,
    model_path: Path | None,
) -> tuple[Path, Path]:
    md_path = case_dir / "rule_card.md"
    tex_path = case_dir / "rule_card.tex"

    witnesses: list[dict[str, Any]] = []
    if model_path is not None and model_path.exists():
        witnesses = _build_rule_witnesses(model_path=model_path, manifest_path=manifest_path, max_witnesses=3)

    md_lines: list[str] = []
    md_lines.append(f"# Rule Card: `{case_id}`")
    md_lines.append("")
    md_lines.append("## Key metrics")
    md_lines.append("")
    md_lines.append(f"- axioms_on: `{', '.join(axioms_on)}`")
    md_lines.append(f"- model_validated: `{model_validated}`")
    md_lines.append(f"- distinct_social_outcomes: `{metrics.get('distinct_social_outcomes')}`")
    md_lines.append(f"- dictatorship_score_max: `{float(metrics.get('dictatorship_score_max', 1.0)):.4f}`")
    md_lines.append(f"- constant_function_rate: `{float(metrics.get('constant_function_rate', 1.0)):.4f}`")
    md_lines.append(f"- neutrality_violation_count: `{metrics.get('neutrality_violation_count')}`")
    md_lines.append("")
    md_lines.append("## Non-triviality report")
    md_lines.append("")
    md_lines.append(f"- passes_non_triviality: `{bool(nontriviality_report.get('passes_non_triviality', False))}`")
    md_lines.append(
        f"- included_reasons: `{', '.join(nontriviality_report.get('included_reasons', [])) or '(none)'}`"
    )
    md_lines.append(
        f"- excluded_reasons: `{', '.join(nontriviality_report.get('excluded_reasons', [])) or '(none)'}`"
    )
    md_lines.append("")
    md_lines.append("## Profile witnesses")
    md_lines.append("")
    for idx, witness in enumerate(witnesses, start=1):
        md_lines.append(f"### Witness {idx}")
        md_lines.append(
            f"- profile_id: `{witness['profile_id']}`; tags: `{', '.join(witness['witness_tags'])}`"
        )
        md_lines.append(f"- voter0 ranking: `{_fmt_perm(tuple(witness['r0']))}`")
        md_lines.append(f"- voter1 ranking: `{_fmt_perm(tuple(witness['r1']))}`")
        md_lines.append(f"- social edges: `{', '.join(witness['social_edges']) or '(none)'}`")
        md_lines.append(
            f"- differs_from_voter0: `{witness['differs_from_voter0']}`, "
            f"differs_from_voter1: `{witness['differs_from_voter1']}`"
        )
        md_lines.append("")
    if not witnesses:
        md_lines.append("- no witness profiles available (model unavailable)")
        md_lines.append("")

    md_path.write_text("\n".join(md_lines).rstrip() + "\n", encoding="utf-8")

    tex_lines: list[str] = []
    tex_lines.append(r"\subsection*{Rule Card: " + _tex_escape(case_id) + "}")
    tex_lines.append(r"\begin{itemize}")
    tex_lines.append(r"\item axioms\_on: \texttt{" + _tex_escape(", ".join(axioms_on)) + "}")
    tex_lines.append(r"\item model\_validated: \texttt{" + _tex_escape(str(model_validated)) + "}")
    tex_lines.append(
        r"\item distinct\_social\_outcomes: \texttt{" + _tex_escape(str(metrics.get("distinct_social_outcomes"))) + "}"
    )
    tex_lines.append(
        r"\item dictatorship\_score\_max: \texttt{"
        + _tex_escape(f"{float(metrics.get('dictatorship_score_max', 1.0)):.4f}")
        + "}"
    )
    tex_lines.append(
        r"\item constant\_function\_rate: \texttt{"
        + _tex_escape(f"{float(metrics.get('constant_function_rate', 1.0)):.4f}")
        + "}"
    )
    tex_lines.append(r"\end{itemize}")
    tex_lines.append(r"\paragraph{Profile witnesses.}")
    tex_lines.append(r"\begin{enumerate}")
    for witness in witnesses:
        tex_lines.append(
            r"\item \texttt{p="
            + _tex_escape(str(witness["profile_id"]))
            + "} tags=\texttt{"
            + _tex_escape(", ".join(witness["witness_tags"]))
            + r"}; "
            + r"$r_0$=\texttt{"
            + _tex_escape(_fmt_perm(tuple(witness["r0"])))
            + r"}, $r_1$=\texttt{"
            + _tex_escape(_fmt_perm(tuple(witness["r1"])))
            + r"}; edges=\texttt{"
            + _tex_escape(", ".join(witness["social_edges"]) or "(none)")
            + r"}."
        )
    if not witnesses:
        tex_lines.append(r"\item no witness profiles available.")
    tex_lines.append(r"\end{enumerate}")
    tex_path.write_text("\n".join(tex_lines).rstrip() + "\n", encoding="utf-8")

    return md_path, tex_path


def _rank_key(candidate: Candidate) -> tuple[float, float, int, str]:
    metrics = candidate.metrics
    return (
        -float(metrics.get("distinct_social_outcomes", 0.0)),
        float(metrics.get("dictatorship_score_max", 1.0)),
        int(metrics.get("neutrality_violation_count", 10**9)),
        candidate.case_id,
    )


def _run_decode_model(case_dir: Path) -> bool:
    cmd = [sys.executable, str(DECODE_MODEL), "--case-dir", str(case_dir)]
    proc = subprocess.run(cmd, capture_output=True, text=True, check=False)
    return proc.returncode == 0


def _relpath(path: Path | None, base: Path) -> str | None:
    if path is None:
        return None
    return os.path.relpath(str(path.resolve()), str(base.resolve()))


def _load_thresholds(path: Path | None) -> dict[str, float]:
    thresholds = dict(DEFAULT_THRESHOLDS)
    if path is None:
        return thresholds
    payload = _load_json(path)
    for key in DEFAULT_THRESHOLDS.keys():
        if key in payload:
            thresholds[key] = float(payload[key])
    return thresholds


def _safe_text_assert(text: str) -> None:
    if "/Users/" in text:
        raise ValueError("gallery output contains disallowed absolute path fragment '/Users/'")
    if re.search(r"[A-Za-z]:\\", text):
        raise ValueError("gallery output contains disallowed Windows absolute path")


def main() -> None:
    ap = argparse.ArgumentParser(description="Build SAT gallery from atlas outputs")
    ap.add_argument("--atlas-outdir", type=Path, required=True, help="Atlas outdir containing atlas.json and case_* dirs")
    ap.add_argument("--outdir", type=Path, default=None, help="Output directory for gallery.json/gallery.md (default: atlas outdir)")
    ap.add_argument("--top-k", type=int, default=5)
    ap.add_argument("--min-k", type=int, default=1)
    ap.add_argument("--unique-by", choices=["none", "equiv_class"], default="equiv_class")
    ap.add_argument("--require-model", dest="require_model", action="store_true", default=True)
    ap.add_argument("--allow-missing-model", action="store_true", help="Allow gallery entries without model.json")
    ap.add_argument(
        "--allow-trivial-fallback",
        action="store_true",
        help="If non-trivial candidates are fewer than min-k, fill with best remaining SAT candidates.",
    )
    ap.add_argument("--thresholds-json", type=Path, default=None)
    ap.add_argument("--dry-run", action="store_true")
    args = ap.parse_args()

    if args.top_k < 1:
        raise ValueError("--top-k must be >= 1")
    if args.min_k < 0:
        raise ValueError("--min-k must be >= 0")
    if args.min_k > args.top_k:
        raise ValueError("--min-k cannot be greater than --top-k")

    atlas_outdir = args.atlas_outdir
    atlas_path = atlas_outdir / "atlas.json"
    if not atlas_path.exists():
        raise FileNotFoundError(f"missing atlas.json: {atlas_path}")

    outdir = args.outdir if args.outdir is not None else atlas_outdir
    outdir.mkdir(parents=True, exist_ok=True)

    require_model = args.require_model and not args.allow_missing_model
    thresholds = _load_thresholds(args.thresholds_json)

    atlas_raw = atlas_path.read_bytes()
    atlas = json.loads(atlas_raw.decode("utf-8"))
    cases = _normalize_cases(atlas)

    sat_cases = sorted(
        [
            case
            for case in cases
            if str(case.get("status", "UNKNOWN")) == "SAT" and bool(case.get("solved", False))
        ],
        key=lambda c: str(c.get("case_id", "")),
    )

    candidates: list[Candidate] = []
    skipped: dict[str, int] = {
        "missing_model": 0,
        "missing_manifest_or_cnf": 0,
        "metrics_error": 0,
        "invalid_model": 0,
    }

    for case in sat_cases:
        case_id = str(case.get("case_id", ""))
        case_dir = atlas_outdir / case_id
        model_path = case_dir / "model.json"
        cnf_path = case_dir / "sen24.cnf"
        manifest_path = case_dir / "sen24.manifest.json"
        rule_path = case_dir / "rule.md"

        if require_model and not model_path.exists():
            skipped["missing_model"] += 1
            continue
        if not cnf_path.exists() or not manifest_path.exists():
            skipped["missing_manifest_or_cnf"] += 1
            continue

        metrics: dict[str, Any]
        validator_stats: dict[str, Any]
        model_validated = False

        if model_path.exists():
            try:
                metrics = _compute_metrics(model_path, manifest_path)
            except Exception:
                skipped["metrics_error"] += 1
                continue
            validator_stats = validate_witness(
                cnf_path=cnf_path,
                model_path=model_path,
                strict_unassigned=True,
            )
            model_validated = bool(validator_stats.get("ok", False))
            if not model_validated:
                skipped["invalid_model"] += 1
                continue
        else:
            metrics = {
                "dictatorship_score_voter0": 1.0,
                "dictatorship_score_voter1": 1.0,
                "dictatorship_score_max": 1.0,
                "neutrality_violation_count": 10**9,
                "distinct_social_outcomes": 0,
                "constant_function_rate": 1.0,
            }
            validator_stats = {
                "ok": False,
                "error": "model.json missing",
            }

        if not rule_path.exists() and model_path.exists() and not args.dry_run:
            _run_decode_model(case_dir)

        nontriviality_report = _build_nontriviality_report(metrics, thresholds)
        non_trivial = bool(nontriviality_report["passes_non_triviality"])
        candidates.append(
            Candidate(
                case_id=case_id,
                case=case,
                case_dir=case_dir,
                metrics=metrics,
                model_validated=model_validated,
                validator_stats=validator_stats,
                non_trivial=non_trivial,
                nontriviality_report=nontriviality_report,
                rule_path=rule_path if rule_path.exists() else None,
                rule_card_md_path=None,
                rule_card_tex_path=None,
                model_path=model_path if model_path.exists() else None,
                cnf_path=cnf_path,
                manifest_path=manifest_path,
            )
        )

    unique_mode = args.unique_by
    has_equiv = all(c.case.get("equiv_class_id") for c in candidates) if candidates else False
    if unique_mode == "equiv_class" and not has_equiv:
        unique_mode = "none"

    deduped: list[Candidate] = []
    if unique_mode == "equiv_class":
        groups: dict[str, list[Candidate]] = {}
        for c in candidates:
            class_id = str(c.case.get("equiv_class_id"))
            groups.setdefault(class_id, []).append(c)

        for class_id in sorted(groups.keys()):
            group = groups[class_id]
            preferred = [g for g in group if str(g.case.get("representative_case", "")) == g.case_id]
            target = preferred if preferred else group
            chosen = sorted(target, key=_rank_key)[0]
            deduped.append(chosen)
    else:
        deduped = list(candidates)

    ranked = sorted(deduped, key=_rank_key)
    non_trivial_ranked = [c for c in ranked if c.non_trivial]
    selected = list(non_trivial_ranked[: args.top_k])
    if len(selected) < args.min_k and args.allow_trivial_fallback:
        for c in ranked:
            if c in selected:
                continue
            selected.append(c)
            if len(selected) >= args.min_k:
                break
        selected = selected[: args.top_k]

    if args.min_k > 0 and len(selected) < args.min_k:
        raise RuntimeError(
            "Could not build gallery with requested non-trivial minimum: "
            f"min_k={args.min_k}, selected={len(selected)}, non_trivial_candidates={len(non_trivial_ranked)}, "
            "set --allow-trivial-fallback to relax this constraint"
        )

    if args.dry_run:
        for idx, c in enumerate(selected, start=1):
            print(
                f"{idx}. {c.case_id} distinct={c.metrics.get('distinct_social_outcomes')} "
                f"dict_max={c.metrics.get('dictatorship_score_max'):.4f} non_trivial={c.non_trivial}"
            )
        print(
            f"dry-run summary: sat_cases={len(sat_cases)} candidates={len(candidates)} "
            f"deduped={len(deduped)} non_trivial={len(non_trivial_ranked)} "
            f"selected={len(selected)} skipped={skipped}"
        )
        return

    entries: list[dict[str, Any]] = []
    md_lines: list[str] = []

    for c in selected:
        case_id = c.case_id
        case = c.case
        rule_path = c.rule_path
        rule_card_md_path, rule_card_tex_path = _write_rule_cards(
            case_id=case_id,
            case_dir=c.case_dir,
            axioms_on=list(case.get("axioms_on", [])),
            metrics=c.metrics,
            nontriviality_report=c.nontriviality_report,
            model_validated=c.model_validated,
            manifest_path=c.manifest_path,
            model_path=c.model_path,
        )

        rule_excerpt: list[str] = []
        if rule_path is not None and rule_path.exists():
            rule_excerpt = rule_path.read_text(encoding="utf-8", errors="ignore").splitlines()[:15]

        entry = {
            "case_id": case_id,
            "equiv_class_id": case.get("equiv_class_id"),
            "orbit_size": case.get("orbit_size"),
            "representative_case": case.get("representative_case"),
            "axioms_on": list(case.get("axioms_on", [])),
            "status": case.get("status"),
            "solved": bool(case.get("solved", False)),
            "non_trivial": c.non_trivial,
            "nontriviality_report": c.nontriviality_report,
            "model_validated": c.model_validated,
            "validator_stats": c.validator_stats,
            "metrics": {
                "dictatorship_score_max": c.metrics.get("dictatorship_score_max"),
                "distinct_social_outcomes": c.metrics.get("distinct_social_outcomes"),
                "constant_function_rate": c.metrics.get("constant_function_rate"),
                "neutrality_violation_count": c.metrics.get("neutrality_violation_count"),
            },
            "files": {
                "rule_md": _relpath(rule_path, outdir),
                "rule_card_md": _relpath(rule_card_md_path, outdir),
                "rule_card_tex": _relpath(rule_card_tex_path, outdir),
                "model_json": _relpath(c.model_path, outdir),
                "sen24_cnf": _relpath(c.cnf_path, outdir),
                "sen24_manifest": _relpath(c.manifest_path, outdir),
            },
            "reproduce": {
                "run_atlas_case": (
                    f"python3 scripts/run_atlas.py --outdir <atlas_outdir> --case-masks {int(case.get('mask_int', -1))} "
                    "--jobs 1 --prune none --emit-proof never"
                ),
                "decode_model": f"python3 scripts/decode_model.py --case-dir <atlas_outdir>/{case_id}",
                "validate_model": (
                    f"python3 scripts/validate_sat_witness.py --cnf <atlas_outdir>/{case_id}/sen24.cnf "
                    f"--model <atlas_outdir>/{case_id}/model.json"
                ),
            },
            "rule_excerpt": rule_excerpt,
        }
        entries.append(entry)

    solver_info = atlas.get("solver_info", {})
    gallery = {
        "gallery_schema_version": GALLERY_SCHEMA_VERSION,
        "generated_utc": datetime.now(timezone.utc).isoformat(),
        "git": {"commit": _probe_git_commit()},
        "python": {"version": sys.version.split()[0]},
        "platform": py_platform.platform(),
        "solver": {
            "path": _sanitize_path_string(solver_info.get("solver_path", "unknown")),
            "version_raw": str(solver_info.get("solver_version_raw", "unknown")),
            "version": str(solver_info.get("solver_version", "unknown")),
            "sha256": str(solver_info.get("solver_sha256", "unknown")),
        },
        "atlas": {
            "atlas_schema_version": atlas.get("atlas_schema_version"),
            "atlas_sha256": _sha256_bytes(atlas_raw),
            "axiom_universe": list(atlas.get("axiom_universe", [])),
            "axiom_bit_order": "bit i corresponds to axiom_universe[i]",
        },
        "selection": {
            "top_k": args.top_k,
            "min_k": args.min_k,
            "unique_by": unique_mode,
            "require_model": require_model,
            "allow_trivial_fallback": bool(args.allow_trivial_fallback),
            "thresholds": thresholds,
            "sat_cases_total": len(sat_cases),
            "candidate_count": len(candidates),
            "deduped_count": len(deduped),
            "non_trivial_count": len(non_trivial_ranked),
            "selected_count": len(entries),
            "skipped": skipped,
        },
        "entries": entries,
    }

    gallery_json_path = outdir / "gallery.json"
    gallery_md_path = outdir / "gallery.md"

    _write_json(gallery_json_path, gallery)

    md_lines.append("# SAT Gallery")
    md_lines.append("")
    md_lines.append("This gallery lists deterministic SAT witnesses selected from atlas outputs under non-triviality heuristics.")
    md_lines.append("")
    md_lines.append("## Reproduce")
    md_lines.append("")
    md_lines.append("```bash")
    md_lines.append("python3 scripts/build_sat_gallery.py --atlas-outdir <atlas_outdir> --top-k 5 --min-k 1")
    md_lines.append("```")
    md_lines.append("")
    md_lines.append("## Selected entries")
    md_lines.append("")
    md_lines.append("| case_id | axioms_on | distinct_social_outcomes | dictatorship_score_max | model_validated |")
    md_lines.append("|---|---|---:|---:|---:|")
    for entry in entries:
        md_lines.append(
            "| "
            f"`{entry['case_id']}` | `{','.join(entry['axioms_on'])}` | "
            f"{entry['metrics']['distinct_social_outcomes']} | "
            f"{float(entry['metrics']['dictatorship_score_max']):.4f} | "
            f"{entry['model_validated']} |"
        )
    if not entries:
        md_lines.append("| (none) | - | - | - | - |")
    md_lines.append("")

    for entry in entries:
        md_lines.append(f"## Entry `{entry['case_id']}`")
        md_lines.append("")
        md_lines.append(f"- axioms_on: `{', '.join(entry['axioms_on'])}`")
        md_lines.append(f"- equiv_class_id: `{entry.get('equiv_class_id')}`")
        md_lines.append(f"- orbit_size: `{entry.get('orbit_size')}`")
        md_lines.append(f"- representative_case: `{entry.get('representative_case')}`")
        md_lines.append(f"- model_validated: `{entry['model_validated']}`")
        md_lines.append(f"- non_trivial: `{entry['non_trivial']}`")
        md_lines.append(
            f"- metrics: distinct=`{entry['metrics']['distinct_social_outcomes']}`, "
            f"dict_max=`{float(entry['metrics']['dictatorship_score_max']):.4f}`, "
            f"constant_rate=`{float(entry['metrics']['constant_function_rate']):.4f}`"
        )
        md_lines.append(
            "- nontriviality: included=`"
            + (", ".join(entry["nontriviality_report"]["included_reasons"]) or "(none)")
            + "`, excluded=`"
            + (", ".join(entry["nontriviality_report"]["excluded_reasons"]) or "(none)")
            + "`"
        )
        md_lines.append(
            f"- files: rule=`{entry['files']['rule_md']}`, model=`{entry['files']['model_json']}`, "
            f"rule_card_md=`{entry['files']['rule_card_md']}`, rule_card_tex=`{entry['files']['rule_card_tex']}`, "
            f"cnf=`{entry['files']['sen24_cnf']}`, manifest=`{entry['files']['sen24_manifest']}`"
        )
        md_lines.append("")
        md_lines.append("### Rule excerpt (first 15 lines)")
        md_lines.append("")
        md_lines.append("```text")
        excerpt = entry.get("rule_excerpt", [])
        if excerpt:
            md_lines.extend(str(line) for line in excerpt)
        else:
            md_lines.append("(rule.md unavailable)")
        md_lines.append("```")
        md_lines.append("")

    gallery_md = "\n".join(md_lines).rstrip() + "\n"

    _safe_text_assert(gallery_json_path.read_text(encoding="utf-8"))
    _safe_text_assert(gallery_md)
    for entry in entries:
        rule_card_md_rel = entry["files"].get("rule_card_md")
        rule_card_tex_rel = entry["files"].get("rule_card_tex")
        if rule_card_md_rel:
            _safe_text_assert((outdir / str(rule_card_md_rel)).read_text(encoding="utf-8"))
        if rule_card_tex_rel:
            _safe_text_assert((outdir / str(rule_card_tex_rel)).read_text(encoding="utf-8"))

    gallery_md_path.write_text(gallery_md, encoding="utf-8")

    print(f"Wrote {gallery_json_path}")
    print(f"Wrote {gallery_md_path}")


if __name__ == "__main__":
    main()
