#!/usr/bin/env python3
from __future__ import annotations

import argparse
import csv
import hashlib
import itertools
import json
import shutil
import subprocess
import sys
import time
from collections import Counter
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

SCRIPT_DIR = Path(__file__).resolve().parent
REPO_ROOT = SCRIPT_DIR.parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

from enumerate_repairs import (  # noqa: E402
    _case_lookup,
    _enumerate_case_repairs,
    _normalize_cases,
    _validate_repairs,
)
from gen_dimacs import run_generation  # noqa: E402


DATE_DEFAULT = "20260401"
SCOPE_NOTE = (
    "This Candidate B experiment stays inside the restricted local-rationality family "
    "defined by no_cycle3 and no_cycle4. It is not evidence about full SocialAcyclic. "
    "See docs/no_cycle_interpretation_note.md and docs/axiom_semantics_scaling.md."
)
BUNDLED_UNIVERSE = ["asymm", "un", "minlib", "no_cycle3", "no_cycle4"]
SPLIT_UNIVERSE = [
    "asymm",
    "un",
    "decisive_voter0",
    "decisive_voter1",
    "no_cycle3",
    "no_cycle4",
]
REPRESENTATIONS = {
    "bundled": BUNDLED_UNIVERSE,
    "split": SPLIT_UNIVERSE,
}
EQUIV_LABEL = "granularity-sensitive under logical equivalence"
STRONGER_LABEL = "possibly explained by stronger split encoding"
INCONCLUSIVE_LABEL = "inconclusive"


def _write_json(path: Path, payload: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def _mask_to_bits(mask: int, width: int) -> str:
    return "".join("1" if ((mask >> i) & 1) else "0" for i in range(width))


def _canonical_list(axioms: list[str], universe: list[str]) -> list[str]:
    order = {ax: i for i, ax in enumerate(universe)}
    return sorted(axioms, key=lambda ax: order[ax])


def _canonical_key(axioms: list[str], universe: list[str]) -> str:
    ordered = _canonical_list(axioms, universe)
    return "+".join(ordered) if ordered else "(empty)"


def _mask_from_axioms(axioms: list[str], universe: list[str]) -> int:
    index = {ax: i for i, ax in enumerate(universe)}
    mask = 0
    for ax in axioms:
        mask |= 1 << index[ax]
    return mask


def _status_from_proc(proc: subprocess.CompletedProcess[str]) -> str:
    if proc.returncode == 10:
        return "SAT"
    if proc.returncode == 20:
        return "UNSAT"
    text = f"{proc.stdout}\n{proc.stderr}".upper()
    if "UNSATISFIABLE" in text:
        return "UNSAT"
    if "SATISFIABLE" in text:
        return "SAT"
    return "UNKNOWN"


def _sha256_file(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as f:
        for chunk in iter(lambda: f.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def _parse_clause_counter(path: Path) -> Counter[tuple[int, ...]]:
    counter: Counter[tuple[int, ...]] = Counter()
    for raw in path.read_text(encoding="utf-8").splitlines():
        line = raw.strip()
        if not line or line.startswith("c") or line.startswith("p "):
            continue
        parts = [int(x) for x in line.split()]
        if not parts or parts[-1] != 0:
            raise ValueError(f"malformed DIMACS clause line in {path}: {raw!r}")
        lits = tuple(sorted(parts[:-1]))
        counter[lits] += 1
    return counter


def _bundled_to_split_axioms(axioms: list[str]) -> list[str]:
    out: list[str] = []
    for ax in BUNDLED_UNIVERSE:
        if ax not in axioms:
            continue
        if ax == "minlib":
            out.extend(["decisive_voter0", "decisive_voter1"])
        else:
            out.append(ax)
    return out


def _minimal_repairs_for_representation(atlas: dict[str, Any]) -> dict[str, dict[str, Any]]:
    cases = _normalize_cases(atlas)
    case_by_mask = _case_lookup(cases)
    width = len(atlas["axiom_universe"])
    out: dict[str, dict[str, Any]] = {}
    for case in sorted(cases, key=lambda c: int(c["mask_int"])):
        if str(case.get("status")) != "UNSAT":
            continue
        repairs_obj = _enumerate_case_repairs(
            case=case,
            case_by_mask=case_by_mask,
            axiom_universe=list(atlas["axiom_universe"]),
        )
        _validate_repairs(
            unsat_mask=int(case["mask_int"]),
            repairs=repairs_obj["mcs_all"],
            case_by_mask=case_by_mask,
            width=width,
        )
        out[str(case["case_id"])] = repairs_obj
    return out


def _render_repairs_list(repairs: list[dict[str, Any]], universe: list[str]) -> list[str]:
    rendered: list[str] = []
    for repair in repairs:
        axioms = _canonical_list(list(repair["remove_axioms"]), universe)
        rendered.append(_canonical_key(axioms, universe))
    return rendered


def _solve_representation(
    *,
    name: str,
    universe: list[str],
    solver: str,
    outdir: Path,
) -> dict[str, Any]:
    rep_dir = outdir / name
    rep_dir.mkdir(parents=True, exist_ok=True)

    cases: list[dict[str, Any]] = []
    width = len(universe)
    for mask in range(1 << width):
        axioms_on = [universe[i] for i in range(width) if (mask >> i) & 1]
        case_id = f"case_{_mask_to_bits(mask, width)}"
        case_dir = rep_dir / case_id
        case_dir.mkdir(parents=True, exist_ok=True)
        cnf_path = case_dir / "sen24.cnf"
        manifest_path = case_dir / "sen24.manifest.json"
        solver_log_path = case_dir / "solver.log"
        summary_path = case_dir / "summary.json"

        manifest = run_generation(
            n=2,
            m=4,
            axiom_names=axioms_on,
            out_path=cnf_path,
            manifest_path=manifest_path,
        )

        t0 = time.perf_counter()
        proc = subprocess.run(
            [solver, str(cnf_path)],
            capture_output=True,
            text=True,
            check=False,
        )
        duration_sec = time.perf_counter() - t0
        status = _status_from_proc(proc)

        log_text = "\n".join(
            [
                f"cmd: {solver} {cnf_path}",
                f"return_code: {proc.returncode}",
                f"duration_sec: {duration_sec:.6f}",
                "",
                "stdout:",
                proc.stdout.rstrip(),
                "",
                "stderr:",
                proc.stderr.rstrip(),
                "",
            ]
        )
        solver_log_path.write_text(log_text, encoding="utf-8")

        summary = {
            "representation": name,
            "case_id": case_id,
            "mask_int": mask,
            "mask_bits": _mask_to_bits(mask, width),
            "axioms_on": axioms_on,
            "axioms_off": [ax for ax in universe if ax not in axioms_on],
            "status": status,
            "solved": status in {"SAT", "UNSAT"},
            "duration_sec": duration_sec,
            "solver": solver,
            "files": {
                "cnf": cnf_path.name,
                "manifest": manifest_path.name,
                "solver_log": solver_log_path.name,
                "summary": summary_path.name,
            },
            "manifest": {
                "encoding": manifest["encoding"],
                "nvars": int(manifest["nvars"]),
                "nclauses": int(manifest["nclauses"]),
                "cnf_sha256": manifest.get("cnf_sha256"),
                "category_counts": manifest["category_counts"],
                "minlib": manifest["minlib"],
            },
        }
        summary_path.write_text(json.dumps(summary, indent=2, sort_keys=True) + "\n", encoding="utf-8")
        cases.append(summary)

    status_counts = Counter(str(case["status"]) for case in cases)
    atlas = {
        "experiment": "candidate_b_minlib_granularity",
        "representation": name,
        "generated_at_utc": datetime.now(timezone.utc).isoformat(),
        "n_voters": 2,
        "n_alternatives": 4,
        "axiom_universe": universe,
        "cases_total": len(cases),
        "status_counts": dict(status_counts),
        "scope_note": SCOPE_NOTE,
        "cases": cases,
    }
    _write_json(rep_dir / "atlas.json", atlas)
    return atlas


def _build_comparison(
    *,
    outdir: Path,
    bundled_atlas: dict[str, Any],
    split_atlas: dict[str, Any],
    bundled_repairs: dict[str, dict[str, Any]],
    split_repairs: dict[str, dict[str, Any]],
) -> dict[str, Any]:
    bundled_cases = {str(c["case_id"]): c for c in _normalize_cases(bundled_atlas)}
    split_cases = {str(c["case_id"]): c for c in _normalize_cases(split_atlas)}

    mapped_rows: list[dict[str, Any]] = []
    mapped_clause_equal = True
    mapped_status_equal = True
    for bundled_case in sorted(bundled_cases.values(), key=lambda c: int(c["mask_int"])):
        bundled_axioms = list(bundled_case["axioms_on"])
        split_axioms = _bundled_to_split_axioms(bundled_axioms)
        split_mask = _mask_from_axioms(split_axioms, SPLIT_UNIVERSE)
        split_case_id = f"case_{_mask_to_bits(split_mask, len(SPLIT_UNIVERSE))}"
        split_case = split_cases[split_case_id]

        bundled_cnf = outdir / "bundled" / str(bundled_case["case_id"]) / "sen24.cnf"
        split_cnf = outdir / "split" / str(split_case["case_id"]) / "sen24.cnf"
        clause_equal = _parse_clause_counter(bundled_cnf) == _parse_clause_counter(split_cnf)
        status_equal = str(bundled_case["status"]) == str(split_case["status"])
        mapped_clause_equal = mapped_clause_equal and clause_equal
        mapped_status_equal = mapped_status_equal and status_equal

        mapped_rows.append(
            {
                "bundled_case_id": bundled_case["case_id"],
                "bundled_package": bundled_axioms,
                "bundled_package_key": _canonical_key(bundled_axioms, BUNDLED_UNIVERSE),
                "split_case_id": split_case["case_id"],
                "split_package": split_axioms,
                "split_package_key": _canonical_key(split_axioms, SPLIT_UNIVERSE),
                "bundled_status": bundled_case["status"],
                "split_status": split_case["status"],
                "status_equal": status_equal,
                "clause_multiset_equal": clause_equal,
            }
        )

    logical_relation = (
        "exact clause-multiset equivalence under the bundled→split mapping"
        if mapped_clause_equal
        else "not exact at the clause-set level"
    )
    logical_classification = (
        "logically equivalent"
        if mapped_clause_equal and mapped_status_equal
        else "strictly stronger or otherwise not equivalent"
    )

    repair_rows: list[dict[str, Any]] = []
    witness_rows: list[dict[str, Any]] = []
    for bundled_case_id, bundled_rep in sorted(bundled_repairs.items()):
        bundled_case = bundled_cases[bundled_case_id]
        split_axioms = _bundled_to_split_axioms(list(bundled_case["axioms_on"]))
        split_case_id = f"case_{_mask_to_bits(_mask_from_axioms(split_axioms, SPLIT_UNIVERSE), len(SPLIT_UNIVERSE))}"
        split_rep = split_repairs[split_case_id]
        bundled_min = _render_repairs_list(bundled_rep["mcs_min_all"], BUNDLED_UNIVERSE)
        split_min = _render_repairs_list(split_rep["mcs_min_all"], SPLIT_UNIVERSE)
        has_bundled_minlib = "minlib" in bundled_min
        has_split_person_specific = (
            "decisive_voter0" in split_min or "decisive_voter1" in split_min
        )
        explanation_changed = has_bundled_minlib and has_split_person_specific
        classification = EQUIV_LABEL if explanation_changed and logical_classification == "logically equivalent" else INCONCLUSIVE_LABEL
        levels: list[int] = []
        if explanation_changed and logical_classification == "logically equivalent":
            levels = [1, 2, 3, 4]
        row = {
            "bundled_case_id": bundled_case_id,
            "bundled_package": list(bundled_case["axioms_on"]),
            "bundled_package_key": _canonical_key(list(bundled_case["axioms_on"]), BUNDLED_UNIVERSE),
            "split_case_id": split_case_id,
            "split_package": split_axioms,
            "split_package_key": _canonical_key(split_axioms, SPLIT_UNIVERSE),
            "bundled_min_repairs": bundled_min,
            "split_min_repairs": split_min,
            "bundled_contains_minlib_singleton": has_bundled_minlib,
            "split_contains_person_specific_singletons": has_split_person_specific,
            "repair_explanation_changed": explanation_changed,
            "classification": classification,
            "evidence_levels": levels,
        }
        repair_rows.append(row)
        if explanation_changed:
            witness_rows.append(row)

    one_sided_rows: list[dict[str, Any]] = []
    for split_case in sorted(split_cases.values(), key=lambda c: int(c["mask_int"])):
        axioms = set(split_case["axioms_on"])
        has0 = "decisive_voter0" in axioms
        has1 = "decisive_voter1" in axioms
        if has0 == has1:
            continue
        one_sided_rows.append(
            {
                "case_id": split_case["case_id"],
                "package": list(split_case["axioms_on"]),
                "package_key": _canonical_key(list(split_case["axioms_on"]), SPLIT_UNIVERSE),
                "status": split_case["status"],
            }
        )

    one_sided_status_counts = Counter(row["status"] for row in one_sided_rows)
    witness = None
    if witness_rows:
        witness = min(
            witness_rows,
            key=lambda row: (
                len(row["bundled_package"]),
                row["bundled_package_key"],
            ),
        )

    comparison = {
        "experiment": "candidate_b_minlib_granularity",
        "generated_at_utc": datetime.now(timezone.utc).isoformat(),
        "date": DATE_DEFAULT,
        "scope_note": SCOPE_NOTE,
        "n_voters": 2,
        "n_alternatives": 4,
        "bundled_universe": BUNDLED_UNIVERSE,
        "split_universe": SPLIT_UNIVERSE,
        "logical_relation": {
            "classification": logical_classification,
            "detail": logical_relation,
            "mapped_cases_total": len(mapped_rows),
            "mapped_status_equal": mapped_status_equal,
            "mapped_clause_multiset_equal": mapped_clause_equal,
        },
        "mapped_cases": mapped_rows,
        "repair_comparison": repair_rows,
        "one_sided_split_cases": {
            "total": len(one_sided_rows),
            "status_counts": dict(one_sided_status_counts),
            "rows": one_sided_rows,
        },
        "candidate_b_assessment": {
            "supported": bool(witness_rows) and logical_classification == "logically equivalent",
            "classification": EQUIV_LABEL if witness_rows and logical_classification == "logically equivalent" else STRONGER_LABEL,
            "evidence_levels": [1, 2, 3, 4] if witness_rows and logical_classification == "logically equivalent" else [],
            "cleanest_witness": witness,
        },
    }
    return comparison


def _write_comparison_csv(path: Path, rows: list[dict[str, Any]]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", encoding="utf-8", newline="") as f:
        writer = csv.writer(f)
        writer.writerow(
            [
                "bundled_case_id",
                "bundled_package_key",
                "split_case_id",
                "split_package_key",
                "bundled_min_repairs",
                "split_min_repairs",
                "repair_explanation_changed",
                "classification",
                "evidence_levels",
            ]
        )
        for row in rows:
            writer.writerow(
                [
                    row["bundled_case_id"],
                    row["bundled_package_key"],
                    row["split_case_id"],
                    row["split_package_key"],
                    ";".join(row["bundled_min_repairs"]),
                    ";".join(row["split_min_repairs"]),
                    "yes" if row["repair_explanation_changed"] else "no",
                    row["classification"],
                    ";".join(str(x) for x in row["evidence_levels"]),
                ]
            )


def _build_summary_md(comparison: dict[str, Any], bundled_atlas: dict[str, Any], split_atlas: dict[str, Any]) -> str:
    assessment = comparison["candidate_b_assessment"]
    witness = assessment["cleanest_witness"]
    bundled_unsat = int(bundled_atlas["status_counts"].get("UNSAT", 0))
    split_unsat = int(split_atlas["status_counts"].get("UNSAT", 0))
    one_sided_counts = comparison["one_sided_split_cases"]["status_counts"]
    lines: list[str] = [
        "# Candidate B Summary",
        "",
        f"**Generated:** {comparison['generated_at_utc']}  ",
        "**Base case:** n=2, m=4 only  ",
        f"**Scope note:** {comparison['scope_note']}",
        "",
        "## Comparison",
        "",
        "- Representation A (bundled): `asymm, un, minlib, no_cycle3, no_cycle4`.",
        "- Representation B (split): `asymm, un, decisive_voter0, decisive_voter1, no_cycle3, no_cycle4`.",
        "- The main comparison stays entirely inside the current `no_cycle3` / `no_cycle4` local-rationality family.",
        "",
        "## Logical relation",
        "",
        f"- Split `minlib` is classified as **{comparison['logical_relation']['classification']}** relative to bundled `minlib` at the base case.",
        f"- Detail: {comparison['logical_relation']['detail']}.",
        f"- Mapped bundled/split cases checked: `{comparison['logical_relation']['mapped_cases_total']}`.",
        "",
        "## Frontier",
        "",
        f"- Bundled UNSAT cases: `{bundled_unsat}`.",
        f"- Split UNSAT cases: `{split_unsat}`.",
        f"- Corresponding bundled→split mapped cases preserve status: `{comparison['logical_relation']['mapped_status_equal']}`.",
        f"- Split one-sided decisive cases status counts: `{dict(one_sided_counts)}`.",
        "",
        "## Repair explanation",
        "",
    ]
    if witness is not None:
        lines.extend(
            [
                f"- Cleanest witness: bundled `{witness['bundled_package_key']}` versus split `{witness['split_package_key']}`.",
                f"- Bundled minimal repairs: `{', '.join(witness['bundled_min_repairs'])}`.",
                f"- Split minimal repairs: `{', '.join(witness['split_min_repairs'])}`.",
                "- This changes the repair explanation from a bundled liberalism repair to person-specific liberalism repairs.",
            ]
        )
    else:
        lines.append("- No clean witness was found.")

    lines.extend(
        [
            "",
            "## Candidate B assessment",
            "",
            f"- Candidate B concrete support: `{assessment['supported']}`.",
            f"- Classification: `{assessment['classification']}`.",
            f"- Evidence levels satisfied: `{assessment['evidence_levels']}`.",
            "",
            "## Conclusion",
            "",
        ]
    )
    if assessment["supported"]:
        lines.extend(
            [
                "- The corresponding bundled and split packages are clause-set equivalent at the base case, so the observed repair difference is not explained by a stronger split encoding.",
                "- The mapped UNSAT frontier is unchanged, but the repair explanation changes when `minlib` is exposed as `decisive_voter0` and `decisive_voter1`.",
                "- This is direct Candidate B evidence inside the restricted local-rationality family.",
            ]
        )
    else:
        lines.extend(
            [
                "- The comparison did not produce direct Candidate B support at the configured evidence levels.",
                "- Any observed difference would need stronger qualification.",
            ]
        )
    return "\n".join(lines).rstrip() + "\n"


def main() -> None:
    ap = argparse.ArgumentParser(description="Run the base-case Candidate B minlib-granularity comparison.")
    ap.add_argument(
        "--outdir",
        type=Path,
        default=REPO_ROOT / "results" / DATE_DEFAULT / "candidate_b_minlib_granularity",
        help="Output directory for Candidate B artifacts.",
    )
    ap.add_argument("--solver", type=str, default="cadical", help="SAT solver executable.")
    args = ap.parse_args()

    solver_path = shutil.which(args.solver)
    if solver_path is None:
        raise FileNotFoundError(f"solver not found on PATH: {args.solver}")

    outdir = args.outdir
    outdir.mkdir(parents=True, exist_ok=True)

    bundled_atlas = _solve_representation(
        name="bundled",
        universe=BUNDLED_UNIVERSE,
        solver=args.solver,
        outdir=outdir,
    )
    split_atlas = _solve_representation(
        name="split",
        universe=SPLIT_UNIVERSE,
        solver=args.solver,
        outdir=outdir,
    )

    bundled_repairs = _minimal_repairs_for_representation(bundled_atlas)
    split_repairs = _minimal_repairs_for_representation(split_atlas)

    comparison = _build_comparison(
        outdir=outdir,
        bundled_atlas=bundled_atlas,
        split_atlas=split_atlas,
        bundled_repairs=bundled_repairs,
        split_repairs=split_repairs,
    )
    _write_json(outdir / "comparison.json", comparison)
    _write_comparison_csv(outdir / "comparison.csv", comparison["repair_comparison"])
    (outdir / "summary.md").write_text(
        _build_summary_md(comparison, bundled_atlas, split_atlas),
        encoding="utf-8",
    )

    print(f"Wrote {outdir / 'bundled' / 'atlas.json'}")
    print(f"Wrote {outdir / 'split' / 'atlas.json'}")
    print(f"Wrote {outdir / 'comparison.json'}")
    print(f"Wrote {outdir / 'comparison.csv'}")
    print(f"Wrote {outdir / 'summary.md'}")


if __name__ == "__main__":
    main()
