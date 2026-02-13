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
    metrics: dict[str, Any]
    model_validated: bool
    validator_stats: dict[str, Any]
    non_trivial: bool
    rule_path: Path | None
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


def _is_non_trivial(metrics: dict[str, Any], thresholds: dict[str, float]) -> bool:
    distinct = float(metrics.get("distinct_social_outcomes", 0.0))
    dictatorship_max = float(metrics.get("dictatorship_score_max", 1.0))
    constant_rate = float(metrics.get("constant_function_rate", 1.0))

    return (
        distinct >= float(thresholds["min_distinct_social_outcomes"])
        and dictatorship_max <= float(thresholds["max_dictatorship_score_max"])
        and constant_rate <= float(thresholds["max_constant_function_rate"])
    )


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

        non_trivial = _is_non_trivial(metrics, thresholds)
        candidates.append(
            Candidate(
                case_id=case_id,
                case=case,
                metrics=metrics,
                model_validated=model_validated,
                validator_stats=validator_stats,
                non_trivial=non_trivial,
                rule_path=rule_path if rule_path.exists() else None,
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
    selected = [c for c in ranked if c.non_trivial][: args.top_k]
    if len(selected) < args.min_k:
        for c in ranked:
            if c in selected:
                continue
            selected.append(c)
            if len(selected) >= args.min_k:
                break
    selected = selected[: args.top_k]

    if args.min_k > 0 and len(selected) < args.min_k:
        raise RuntimeError(
            f"Could not build gallery with min_k={args.min_k}; selected={len(selected)}, sat_candidates={len(ranked)}"
        )

    if args.dry_run:
        for idx, c in enumerate(selected, start=1):
            print(
                f"{idx}. {c.case_id} distinct={c.metrics.get('distinct_social_outcomes')} "
                f"dict_max={c.metrics.get('dictatorship_score_max'):.4f} non_trivial={c.non_trivial}"
            )
        print(
            f"dry-run summary: sat_cases={len(sat_cases)} candidates={len(candidates)} "
            f"deduped={len(deduped)} selected={len(selected)} skipped={skipped}"
        )
        return

    entries: list[dict[str, Any]] = []
    md_lines: list[str] = []

    for c in selected:
        case_id = c.case_id
        case = c.case
        rule_path = c.rule_path

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
            "thresholds": thresholds,
            "sat_cases_total": len(sat_cases),
            "candidate_count": len(candidates),
            "deduped_count": len(deduped),
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
        md_lines.append(
            f"- metrics: distinct=`{entry['metrics']['distinct_social_outcomes']}`, "
            f"dict_max=`{float(entry['metrics']['dictatorship_score_max']):.4f}`, "
            f"constant_rate=`{float(entry['metrics']['constant_function_rate']):.4f}`"
        )
        md_lines.append(
            f"- files: rule=`{entry['files']['rule_md']}`, model=`{entry['files']['model_json']}`, "
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

    gallery_md_path.write_text(gallery_md, encoding="utf-8")

    print(f"Wrote {gallery_json_path}")
    print(f"Wrote {gallery_md_path}")


if __name__ == "__main__":
    main()
