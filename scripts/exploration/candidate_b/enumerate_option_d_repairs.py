#!/usr/bin/env python3
"""
Enumerate raw lever-level inclusion-minimal repairs for Option D.

Scope is deliberately narrow:
  * Option D's legacy-style two-series encoder only;
  * cases (2,4) and (2,5) only by default;
  * bundled minlib versus its two-lever split image;
  * no Option C repair enumeration, pair selectors, all-voter split, or Lean
    integration. Option C Step 0 for (3,4) is handled separately.

Outputs are local exploratory reports under /tmp by default. This is not a
general-purpose MCS framework.
"""

from __future__ import annotations

import argparse
import itertools
import json
import shutil
import subprocess
import sys
import time
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

HERE = Path(__file__).resolve().parent
if str(HERE) not in sys.path:
    sys.path.insert(0, str(HERE))

import option_d_encoder  # noqa: E402
from step0_equiv_check import (  # noqa: E402
    BUNDLED_PACKAGE,
    SCOPE_STATEMENT,
    TRANSPORT_MAP,
    _package_id,
    _split_package,
)

DEFAULT_CASES = [(2, 4), (2, 5)]

CLASS_NONCANONICAL = "noncanonical_persists"
CLASS_CANONICAL = "canonical_preserved"
CLASS_STATUS_NOT_UNSAT = "status_not_unsat"
CLASS_INCONCLUSIVE = "inconclusive"


def _canonical_subset(items: set[str], universe: list[str]) -> list[str]:
    return [item for item in universe if item in items]


def _write_clause_fragments(
    *,
    n: int,
    m: int,
    active_levers: list[str],
    workdir: Path,
) -> tuple[dict[str, Path], dict[str, int], int]:
    """Build once, then split the encoder's canonical contiguous lever blocks."""
    clauses, nvars, per_lever = option_d_encoder.build_clauses(n, m, active_levers)
    fragment_paths: dict[str, Path] = {}
    offset = 0
    for lever, count in per_lever.items():
        path = workdir / f"{lever}.dimacs-fragment"
        with path.open("w", encoding="ascii") as out:
            for clause in clauses[offset : offset + count]:
                out.write(" ".join(str(lit) for lit in clause))
                out.write(" 0\n")
        fragment_paths[lever] = path
        offset += count
    if offset != len(clauses):
        raise RuntimeError(
            f"lever fragment counts cover {offset} clauses, but encoder returned {len(clauses)}"
        )
    return fragment_paths, per_lever, nvars


def _write_subset_cnf(
    *,
    path: Path,
    retained_levers: list[str],
    fragment_paths: dict[str, Path],
    per_lever_counts: dict[str, int],
    nvars: int,
) -> int:
    nclauses = sum(per_lever_counts[lever] for lever in retained_levers)
    with path.open("wb") as out:
        out.write(f"p cnf {nvars} {nclauses}\n".encode("ascii"))
        for lever in retained_levers:
            with fragment_paths[lever].open("rb") as fragment:
                shutil.copyfileobj(fragment, out, length=1024 * 1024)
    return nclauses


def _solver_status(proc: subprocess.CompletedProcess[str]) -> str | None:
    if proc.returncode == 10:
        return "SAT"
    if proc.returncode == 20:
        return "UNSAT"
    text = f"{proc.stdout}\n{proc.stderr}".upper()
    if "UNSATISFIABLE" in text:
        return "UNSAT"
    if "SATISFIABLE" in text:
        return "SAT"
    return None


def _solve(
    cnf_path: Path,
    *,
    solver_path: str,
    timeout_sec: float,
) -> dict[str, Any]:
    started = time.perf_counter()
    try:
        proc = subprocess.run(
            [solver_path, str(cnf_path)],
            capture_output=True,
            text=True,
            check=False,
            timeout=timeout_sec,
        )
    except subprocess.TimeoutExpired:
        duration = time.perf_counter() - started
        return {
            "status": None,
            "method": "solver",
            "duration_sec": duration,
            "detail": f"solver timed out after {timeout_sec:.3f}s",
        }
    duration = time.perf_counter() - started
    status = _solver_status(proc)
    detail = f"rc={proc.returncode}"
    if status is None:
        detail += "; unrecognized solver output"
    return {
        "status": status,
        "method": "solver",
        "duration_sec": duration,
        "detail": detail,
    }


def _all_strict_subsets(repair: set[str]) -> list[frozenset[str]]:
    out: list[frozenset[str]] = []
    ordered = sorted(repair)
    for size in range(len(ordered)):
        out.extend(frozenset(xs) for xs in itertools.combinations(ordered, size))
    return out


def _enumerate_repairs(
    *,
    n: int,
    m: int,
    representation: str,
    active_levers: list[str],
    solver_path: str,
    solve_timeout_sec: float,
    max_representation_sec: float,
    workdir: Path,
) -> dict[str, Any]:
    workdir.mkdir(parents=True, exist_ok=True)
    build_started = time.perf_counter()
    fragments, per_lever_counts, nvars = _write_clause_fragments(
        n=n,
        m=m,
        active_levers=active_levers,
        workdir=workdir,
    )
    build_duration = time.perf_counter() - build_started

    cnf_path = workdir / "current.cnf"
    records: dict[frozenset[str], dict[str, Any]] = {}
    minimal_repairs: list[frozenset[str]] = []
    unresolved_sat_candidates: list[frozenset[str]] = []
    stopped_reason: str | None = None
    enumeration_started = time.perf_counter()

    all_removals = [
        frozenset(combo)
        for size in range(len(active_levers) + 1)
        for combo in itertools.combinations(active_levers, size)
    ]
    for removal in all_removals:
        elapsed = time.perf_counter() - enumeration_started
        if elapsed > max_representation_sec:
            stopped_reason = (
                f"representation time budget exceeded after {elapsed:.3f}s "
                f"(budget {max_representation_sec:.3f}s)"
            )
            break

        containing_repair = next(
            (repair for repair in minimal_repairs if repair.issubset(removal)),
            None,
        )
        retained = [lever for lever in active_levers if lever not in removal]
        ordered_removal = _canonical_subset(set(removal), active_levers)
        if containing_repair is not None:
            records[removal] = {
                "removed_levers": ordered_removal,
                "retained_levers": retained,
                "status": "SAT",
                "method": "inferred_by_clause_removal_monotonicity",
                "inferred_from_repair": _canonical_subset(
                    set(containing_repair), active_levers
                ),
                "nclauses": sum(per_lever_counts[x] for x in retained),
                "duration_sec": 0.0,
                "detail": "A known SAT repair is a subset of this removal set.",
            }
            continue

        nclauses = _write_subset_cnf(
            path=cnf_path,
            retained_levers=retained,
            fragment_paths=fragments,
            per_lever_counts=per_lever_counts,
            nvars=nvars,
        )
        solve_result = _solve(
            cnf_path,
            solver_path=solver_path,
            timeout_sec=solve_timeout_sec,
        )
        record = {
            "removed_levers": ordered_removal,
            "retained_levers": retained,
            "status": solve_result["status"],
            "method": solve_result["method"],
            "nclauses": nclauses,
            "duration_sec": solve_result["duration_sec"],
            "detail": solve_result["detail"],
        }
        records[removal] = record

        if solve_result["status"] == "SAT":
            strict_subset_statuses = [
                records[subset]["status"]
                for subset in _all_strict_subsets(set(removal))
                if subset in records
            ]
            expected_subsets = (1 << len(removal)) - 1
            if (
                len(strict_subset_statuses) == expected_subsets
                and all(status == "UNSAT" for status in strict_subset_statuses)
            ):
                minimal_repairs.append(removal)
            else:
                unresolved_sat_candidates.append(removal)

    if stopped_reason is not None:
        for removal in all_removals:
            if removal in records:
                continue
            retained = [lever for lever in active_levers if lever not in removal]
            records[removal] = {
                "removed_levers": _canonical_subset(set(removal), active_levers),
                "retained_levers": retained,
                "status": None,
                "method": "not_tested",
                "nclauses": sum(per_lever_counts[x] for x in retained),
                "duration_sec": 0.0,
                "detail": stopped_reason,
            }

    ordered_records = [records[removal] for removal in all_removals]
    unknown_count = sum(record["status"] not in {"SAT", "UNSAT"} for record in ordered_records)
    complete = unknown_count == 0 and not unresolved_sat_candidates
    base_record = records[frozenset()]
    return {
        "representation": representation,
        "active_levers": active_levers,
        "package_identifier": _package_id(active_levers),
        "status_before_repair": base_record["status"],
        "status_before_repair_detail": base_record["detail"],
        "raw_minimal_repairs": [
            _canonical_subset(set(repair), active_levers)
            for repair in minimal_repairs
        ],
        "enumeration_complete": complete,
        "unknown_subset_count": unknown_count,
        "unresolved_sat_candidates": [
            _canonical_subset(set(repair), active_levers)
            for repair in unresolved_sat_candidates
        ],
        "stopped_reason": stopped_reason,
        "encoder": option_d_encoder.ENCODING_LABEL,
        "nvars": nvars,
        "per_lever_clause_counts": per_lever_counts,
        "fragment_build_duration_sec": build_duration,
        "enumeration_duration_sec": time.perf_counter() - enumeration_started,
        "subsets_total": len(all_removals),
        "subsets_solved": sum(record["method"] == "solver" for record in ordered_records),
        "subsets_inferred": sum(
            record["method"] == "inferred_by_clause_removal_monotonicity"
            for record in ordered_records
        ),
        "subset_statuses": ordered_records,
    }


def _transport_repairs(
    repairs: list[list[str]],
    split_levers: list[str],
) -> list[list[str]]:
    transported: set[tuple[str, ...]] = set()
    for repair in repairs:
        image: set[str] = set()
        for lever in repair:
            image.update(TRANSPORT_MAP[lever])
        transported.add(tuple(_canonical_subset(image, split_levers)))
    return [list(repair) for repair in sorted(transported)]


def _repair_family(repairs: list[list[str]]) -> set[frozenset[str]]:
    return {frozenset(repair) for repair in repairs}


def _classify_case(
    bundled: dict[str, Any],
    split: dict[str, Any],
    transported: list[list[str]],
) -> tuple[str, str]:
    b_status = bundled["status_before_repair"]
    s_status = split["status_before_repair"]
    if b_status != "UNSAT" or s_status != "UNSAT":
        return (
            CLASS_STATUS_NOT_UNSAT,
            "Repair comparison requires both active packages to be UNSAT, "
            f"but bundled={b_status} and split={s_status}.",
        )
    if not bundled["enumeration_complete"] or not split["enumeration_complete"]:
        reasons = [
            reason
            for reason in (bundled.get("stopped_reason"), split.get("stopped_reason"))
            if reason
        ]
        suffix = f" Reasons: {'; '.join(reasons)}" if reasons else ""
        return (
            CLASS_INCONCLUSIVE,
            "At least one representation has unknown subset statuses or an "
            f"unresolved SAT minimality check.{suffix}",
        )
    equal = _repair_family(transported) == _repair_family(split["raw_minimal_repairs"])
    if equal:
        return (
            CLASS_CANONICAL,
            "The transported bundled raw repair family equals the split raw "
            "repair family under π for this case.",
        )
    return (
        CLASS_NONCANONICAL,
        "The transported bundled raw repair family differs from the split raw "
        "repair family under π; representation-granularity non-canonicity persists.",
    )


def _run_case(
    *,
    n: int,
    m: int,
    outdir: Path,
    solver_path: str,
    solve_timeout_sec: float,
    max_representation_sec: float,
    keep_work: bool,
) -> dict[str, Any]:
    bundled_levers = list(BUNDLED_PACKAGE)
    split_levers = _split_package(bundled_levers)
    case_workdir = outdir / "_work" / f"n{n}_m{m}"

    bundled = _enumerate_repairs(
        n=n,
        m=m,
        representation="bundled",
        active_levers=bundled_levers,
        solver_path=solver_path,
        solve_timeout_sec=solve_timeout_sec,
        max_representation_sec=max_representation_sec,
        workdir=case_workdir / "bundled",
    )
    split = _enumerate_repairs(
        n=n,
        m=m,
        representation="split",
        active_levers=split_levers,
        solver_path=solver_path,
        solve_timeout_sec=solve_timeout_sec,
        max_representation_sec=max_representation_sec,
        workdir=case_workdir / "split",
    )
    transported = _transport_repairs(bundled["raw_minimal_repairs"], split_levers)
    equal = _repair_family(transported) == _repair_family(split["raw_minimal_repairs"])
    classification, explanation = _classify_case(bundled, split, transported)

    if not keep_work:
        shutil.rmtree(case_workdir, ignore_errors=True)

    return {
        "case": {"n": n, "m": m},
        "track": "option_d_positive",
        "bundled_package_identifier": bundled["package_identifier"],
        "split_package_identifier": split["package_identifier"],
        "active_bundled_levers": bundled_levers,
        "active_split_levers": split_levers,
        "transport_map": {lever: list(image) for lever, image in TRANSPORT_MAP.items()},
        "transport_map_note": (
            "π is a lever correspondence / repair-transport map, not a semantic "
            "equivalence claim."
        ),
        "bundled_status_before_repair": bundled["status_before_repair"],
        "split_status_before_repair": split["status_before_repair"],
        "bundled_raw_minimal_repairs": bundled["raw_minimal_repairs"],
        "split_raw_minimal_repairs": split["raw_minimal_repairs"],
        "transported_bundled_repairs": transported,
        "transported_bundled_repairs_equal_split_repairs": equal,
        "classification": classification,
        "explanation": explanation,
        "local_rationality_scope": SCOPE_STATEMENT,
        "bundled_enumeration": bundled,
        "split_enumeration": split,
    }


def _summary_md(payload: dict[str, Any]) -> str:
    lines = [
        "# M2.1 Option D raw repair enumeration",
        "",
        f"Generated: {payload['generated_at_utc']}",
        "",
        f"Scope: {payload['local_rationality_scope']}",
        "",
        "| case | classification | bundled repairs | split repairs | transported = split |",
        "| --- | --- | --- | --- | --- |",
    ]
    for case in payload["cases"]:
        dims = case["case"]
        lines.append(
            f"| ({dims['n']},{dims['m']}) | `{case['classification']}` | "
            f"`{case['bundled_raw_minimal_repairs']}` | "
            f"`{case['split_raw_minimal_repairs']}` | "
            f"{case['transported_bundled_repairs_equal_split_repairs']} |"
        )
    lines.extend(
        [
            "",
            "π is a lever correspondence / repair-transport map, not a semantic "
            "equivalence claim.",
            "",
            "Option C Step 0 for (3,4) is handled separately and is classified "
            "as sat_equiv_only. Option C repair enumeration is not authorized or "
            "implemented in this script. No top-level script promotion is part "
            "of this experiment.",
            "",
        ]
    )
    for case in payload["cases"]:
        dims = case["case"]
        lines.extend(
            [
                f"## ({dims['n']},{dims['m']})",
                "",
                f"- Bundled status before repair: `{case['bundled_status_before_repair']}`",
                f"- Split status before repair: `{case['split_status_before_repair']}`",
                f"- Bundled raw minimal repairs: `{case['bundled_raw_minimal_repairs']}`",
                f"- Split raw minimal repairs: `{case['split_raw_minimal_repairs']}`",
                f"- Transported bundled repairs: `{case['transported_bundled_repairs']}`",
                f"- Equality: `{case['transported_bundled_repairs_equal_split_repairs']}`",
                f"- Classification: `{case['classification']}`",
                f"- Explanation: {case['explanation']}",
                "",
            ]
        )
    return "\n".join(lines).rstrip() + "\n"


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--outdir",
        type=Path,
        default=Path("/tmp/candidate_b_option_d_repairs"),
    )
    parser.add_argument(
        "--cases",
        default=",".join(f"{n}:{m}" for n, m in DEFAULT_CASES),
    )
    parser.add_argument("--solver", default="cadical")
    parser.add_argument("--solve-timeout-sec", type=float, default=120.0)
    parser.add_argument("--max-representation-sec", type=float, default=900.0)
    parser.add_argument("--keep-work", action="store_true")
    args = parser.parse_args()

    solver_path = shutil.which(args.solver)
    if solver_path is None:
        raise SystemExit(f"solver '{args.solver}' is not on PATH")

    cases: list[tuple[int, int]] = []
    for token in args.cases.split(","):
        n_text, m_text = token.strip().split(":")
        case = (int(n_text), int(m_text))
        if case not in DEFAULT_CASES:
            raise SystemExit(
                f"case {case} is outside the authorized Option D scope {DEFAULT_CASES}"
            )
        cases.append(case)

    args.outdir.mkdir(parents=True, exist_ok=True)
    case_reports = [
        _run_case(
            n=n,
            m=m,
            outdir=args.outdir,
            solver_path=solver_path,
            solve_timeout_sec=args.solve_timeout_sec,
            max_representation_sec=args.max_representation_sec,
            keep_work=args.keep_work,
        )
        for n, m in cases
    ]
    payload = {
        "experiment": "m2.1_option_d_raw_repair_enumeration",
        "generated_at_utc": datetime.now(timezone.utc).isoformat(),
        "encoder": option_d_encoder.ENCODING_LABEL,
        "solver": {"requested": args.solver, "resolved_path": solver_path},
        "transport_map": {lever: list(image) for lever, image in TRANSPORT_MAP.items()},
        "transport_map_note": (
            "π is a lever correspondence / repair-transport map, not a semantic "
            "equivalence claim."
        ),
        "local_rationality_scope": SCOPE_STATEMENT,
        "option_c_repair_enumeration": (
            "not_authorized_not_implemented_here"
        ),
        "n3_m4_step0_status": "handled_separately_sat_equiv_only",
        "top_level_scripts_promotion": False,
        "cases": case_reports,
    }

    json_path = args.outdir / "option_d_repairs.json"
    summary_path = args.outdir / "option_d_repairs_summary.md"
    json_path.write_text(
        json.dumps(payload, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    summary_path.write_text(_summary_md(payload), encoding="utf-8")
    print(f"Wrote {json_path}")
    print(f"Wrote {summary_path}")
    for case in case_reports:
        dims = case["case"]
        print(
            f"  ({dims['n']},{dims['m']}): {case['classification']}; "
            f"bundled={case['bundled_raw_minimal_repairs']}; "
            f"split={case['split_raw_minimal_repairs']}"
        )
    print(
        "Option C Step 0 for (3,4) is handled separately as sat_equiv_only; "
        "Option C repair enumeration is not authorized or implemented here; "
        "no top-level promotion occurred."
    )


if __name__ == "__main__":
    main()
