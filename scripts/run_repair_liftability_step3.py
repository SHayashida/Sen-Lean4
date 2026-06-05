#!/usr/bin/env python3
"""Step 3: Local minimality checks for base-case repairs in larger cases.

For each (A, R, A\R) triple from Step 1 and each target case from Step 2
where A\R is SAT, test whether R is locally minimal in the larger case.

Definition: R is locally minimal in a larger case iff
  (1) A\R is SAT in the larger case   (confirmed by Step 2), AND
  (2) for every r ∈ R, A \ (R \ {r}) is UNSAT in the larger case

Since all base-case MCS are size-1, R \ {r} = {} for the single element r,
so the test package is A \ {} = A (the original UNSAT base package).

Usage (from repo root):
    python3 scripts/run_repair_liftability_step3.py \\
        --triples results/20260401/repair_liftability/base_triples.json \\
        --step2   results/20260401/repair_liftability/liftability_step2.json \\
        --date    20260401 \\
        --outdir  results/20260401/repair_liftability

See docs/experiment_protocol_repair_liftability.md for Step 3 specification.
See docs/no_cycle_interpretation_note.md for scope restrictions.
"""
from __future__ import annotations

import argparse
import csv
import json
import shlex
import subprocess
import sys
import time
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

SCRIPT_DIR = Path(__file__).resolve().parent
REPO_ROOT = SCRIPT_DIR.parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

from gen_dimacs import run_generation  # noqa: E402
from run_atlas import _build_solver_cmd, _extract_status  # noqa: E402

# ── constants ─────────────────────────────────────────────────────────────────

CANONICAL_FAMILY: list[str] = ["asymm", "un", "minlib", "no_cycle3", "no_cycle4"]

SCOPE_NOTE = (
    "no_cycle3 and no_cycle4 are treated as local-rationality approximations, "
    "not full SocialAcyclic. Conclusions are valid only within that restricted "
    "local-rationality family. "
    "See docs/no_cycle_interpretation_note.md and docs/axiom_semantics_scaling.md."
)

DEFAULT_SOLVER = "cadical"

TARGET_CASE_DIMS: dict[str, tuple[int, int]] = {
    "n2_m5": (2, 5),
    "n3_m4": (3, 4),
}

# ── helpers ───────────────────────────────────────────────────────────────────


def _load_json(path: Path) -> Any:
    return json.loads(path.read_text(encoding="utf-8"))


def _write_json(path: Path, payload: Any) -> None:
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def _safe_rel(path: Path) -> str:
    try:
        return str(path.relative_to(REPO_ROOT))
    except ValueError:
        return str(path)


def _canonical_key(axioms: list[str]) -> str:
    order = {ax: i for i, ax in enumerate(CANONICAL_FAMILY)}
    return "+".join(sorted(axioms, key=lambda ax: order[ax])) if axioms else "(empty)"


def _canonical_list(axioms: list[str]) -> list[str]:
    order = {ax: i for i, ax in enumerate(CANONICAL_FAMILY)}
    return sorted(axioms, key=lambda ax: order[ax])


def _write_solver_log(
    path: Path,
    *,
    cmd: list[str],
    return_code: int | None,
    stdout: str,
    stderr: str,
    duration_sec: float,
    error: str | None = None,
) -> None:
    lines = [
        "command: " + " ".join(shlex.quote(x) for x in cmd),
        f"return_code: {return_code}",
        f"duration_sec: {duration_sec:.6f}",
    ]
    if error is not None:
        lines.append(f"error: {error}")
    lines += ["----- STDOUT -----", stdout.rstrip("\n"), "----- STDERR -----", stderr.rstrip("\n")]
    path.write_text("\n".join(lines).rstrip() + "\n", encoding="utf-8")


# ── SAT solver call ───────────────────────────────────────────────────────────


def _solve(cnf_path: Path, *, solver: str, log_path: Path) -> tuple[str, float]:
    """Run solver, write log, return (status, duration_sec)."""
    proof_path = cnf_path.with_suffix(".proof.lrat")
    model_path = cnf_path.with_suffix(".model.txt")
    cmd = _build_solver_cmd(
        solver=solver,
        solver_template=None,
        cnf_path=cnf_path,
        proof_path=proof_path,
        model_path=model_path,
        with_proof=False,
    )
    t0 = time.perf_counter()
    try:
        proc = subprocess.run(cmd, capture_output=True, text=True, check=False)
        duration = time.perf_counter() - t0
        status = _extract_status(f"{proc.stdout}\n{proc.stderr}", proc.returncode)
        _write_solver_log(
            log_path, cmd=cmd, return_code=proc.returncode,
            stdout=proc.stdout, stderr=proc.stderr, duration_sec=duration,
        )
    except FileNotFoundError as ex:
        duration = time.perf_counter() - t0
        status = "UNKNOWN"
        _write_solver_log(
            log_path, cmd=cmd, return_code=None,
            stdout="", stderr="", duration_sec=duration, error=str(ex),
        )
    return status, duration


# ── cache: avoid re-solving identical (axiom_set, target_case) ────────────────

class SolveCache:
    def __init__(self, cnf_root: Path, solver: str) -> None:
        self._cache: dict[tuple[str, str], tuple[str, str, str]] = {}
        self._cnf_root = cnf_root
        self._solver = solver

    def solve(
        self,
        axioms: list[str],
        target_label: str,
    ) -> tuple[str, str, str]:
        """Return (sat_status, cnf_rel_path, manifest_rel_path), solving if not cached."""
        key = (_canonical_key(axioms), target_label)
        if key in self._cache:
            return self._cache[key]

        n, m = TARGET_CASE_DIMS[target_label]
        safe_key = _canonical_key(axioms).replace("+", "_")
        case_dir = self._cnf_root / target_label / safe_key
        case_dir.mkdir(parents=True, exist_ok=True)
        cnf_path = case_dir / "test.cnf"
        manifest_path = case_dir / "test.manifest.json"
        log_path = case_dir / "solver.log"

        run_generation(
            n=n, m=m,
            axiom_names=_canonical_list(axioms),
            out_path=cnf_path,
            manifest_path=manifest_path,
        )
        status, _ = _solve(cnf_path, solver=self._solver, log_path=log_path)

        result = (status, _safe_rel(cnf_path), _safe_rel(manifest_path))
        self._cache[key] = result
        return result


# ── core logic ────────────────────────────────────────────────────────────────


def run_step3(
    *,
    triples_path: Path,
    step2_path: Path,
    outdir: Path,
    date_str: str,
    solver: str,
) -> dict[str, Any]:

    triples_doc = _load_json(triples_path)
    step2_doc = _load_json(step2_path)

    # index Step 1 triples by (base_package_key, base_mcs_key)
    triple_index: dict[tuple[str, str], dict[str, Any]] = {}
    for t in triples_doc["triples"]:
        triple_index[(t["base_package_key"], t["base_mcs_key"])] = t

    # filter Step 2 rows to SAT only
    s2_sat_rows = [r for r in step2_doc["rows"] if r["sat_status"] == "SAT"]
    s2_skipped = [r for r in step2_doc["rows"] if r["sat_status"] != "SAT"]

    cnf_root = outdir / "step3_cnfs"
    cache = SolveCache(cnf_root, solver)

    element_rows: list[dict[str, Any]] = []
    aggregate_rows: list[dict[str, Any]] = []

    seen_elem: set[tuple[str, str, str, str]] = set()
    seen_agg: set[tuple[str, str, str]] = set()

    for s2row in s2_sat_rows:
        bpk: str = s2row["base_package_key"]
        mcs_k: str = s2row["base_mcs_key"]
        target: str = s2row["target_case"]
        repaired_pkg_key: str = s2row["repaired_package_key"]

        triple = triple_index[(bpk, mcs_k)]
        base_pkg: list[str] = list(triple["base_package"])
        base_mcs: list[str] = list(triple["base_mcs"])
        repaired_pkg: list[str] = list(triple["repaired_package"])

        agg_dedup = (bpk, mcs_k, target)
        if agg_dedup in seen_agg:
            raise RuntimeError(f"Duplicate aggregate row: {agg_dedup}")
        seen_agg.add(agg_dedup)

        # ── element-level checks ──────────────────────────────────────────
        elem_results: list[dict[str, Any]] = []
        for r_elem in base_mcs:
            elem_dedup = (bpk, mcs_k, target, r_elem)
            if elem_dedup in seen_elem:
                raise RuntimeError(f"Duplicate element row: {elem_dedup}")
            seen_elem.add(elem_dedup)

            # test_package = A \ (R \ {r}) = A \ (R - {r})
            # R \ {r}: remove r_elem from base_mcs
            r_minus_r_elem = [x for x in base_mcs if x != r_elem]
            # A \ (R \ {r}): remove (R \ {r}) from A
            r_minus_set = set(r_minus_r_elem)
            test_pkg = _canonical_list([ax for ax in base_pkg if ax not in r_minus_set])
            test_pkg_key = _canonical_key(test_pkg)

            sat_status, cnf_rel, manifest_rel = cache.solve(test_pkg, target)

            if sat_status not in {"SAT", "UNSAT"}:
                raise RuntimeError(
                    f"Non-decisive solver status '{sat_status}' for "
                    f"test_pkg={test_pkg_key}, target={target}. "
                    "Ensure solver is installed."
                )

            elem_row: dict[str, Any] = {
                "source_case": "n2_m4",
                "target_case": target,
                "base_package": base_pkg,
                "base_package_key": bpk,
                "base_mcs": base_mcs,
                "base_mcs_key": mcs_k,
                "removed_element": r_elem,
                "r_minus_removed": r_minus_r_elem,
                "test_package": test_pkg,
                "test_package_key": test_pkg_key,
                "sat_status": sat_status,
                "solver": solver,
                "cnf_path": cnf_rel,
                "manifest_path": manifest_rel,
                "notes": (
                    f"test_package = A \\ (R \\ {{r}}) = A \\ {r_minus_r_elem or '{}'}. "
                    "UNSAT required for local minimality. " + SCOPE_NOTE
                ),
            }
            element_rows.append(elem_row)
            elem_results.append(elem_row)

        # ── aggregate ─────────────────────────────────────────────────────
        n_unsat = sum(1 for e in elem_results if e["sat_status"] == "UNSAT")
        n_sat = sum(1 for e in elem_results if e["sat_status"] == "SAT")
        locally_minimal = (n_sat == 0) and (len(elem_results) == len(base_mcs))
        witnesses = [e["removed_element"] for e in elem_results if e["sat_status"] == "SAT"]

        aggregate_rows.append({
            "source_case": "n2_m4",
            "target_case": target,
            "base_package": base_pkg,
            "base_package_key": bpk,
            "base_mcs": base_mcs,
            "base_mcs_key": mcs_k,
            "repaired_package": repaired_pkg,
            "repaired_package_key": repaired_pkg_key,
            "base_repair_size": len(base_mcs),
            "step2_sat_status": "SAT",
            "all_element_checks_completed": True,
            "num_element_checks": len(elem_results),
            "num_unsat_checks": n_unsat,
            "num_sat_checks": n_sat,
            "locally_minimal": locally_minimal,
            "witness_removed_elements_for_failure": witnesses,
            "notes": SCOPE_NOTE,
        })

    # ── validation ───────────────────────────────────────────────────────────
    exp_agg = len(s2_sat_rows)
    if len(aggregate_rows) != exp_agg:
        raise RuntimeError(f"Expected {exp_agg} aggregate rows, got {len(aggregate_rows)}.")

    exp_elem = sum(len(t["base_mcs"]) for _, t in
                   [(r, triple_index[(r["base_package_key"], r["base_mcs_key"])]) for r in s2_sat_rows])
    if len(element_rows) != exp_elem:
        raise RuntimeError(f"Expected {exp_elem} element rows, got {len(element_rows)}.")

    for agg in aggregate_rows:
        correct_lm = (agg["num_sat_checks"] == 0)
        if agg["locally_minimal"] != correct_lm:
            raise RuntimeError(
                f"Inconsistent locally_minimal for "
                f"({agg['base_package_key']},{agg['base_mcs_key']},{agg['target_case']})"
            )

    # ── summary stats ────────────────────────────────────────────────────────
    by_target: dict[str, dict[str, Any]] = {}
    for tc in TARGET_CASE_DIMS:
        tc_agg = [r for r in aggregate_rows if r["target_case"] == tc]
        by_target[tc] = {
            "n_aggregate_rows": len(tc_agg),
            "locally_minimal": sum(1 for r in tc_agg if r["locally_minimal"]),
            "not_locally_minimal": sum(1 for r in tc_agg if not r["locally_minimal"]),
        }

    outcome_a = all(r["locally_minimal"] for r in aggregate_rows)
    outcome = "A" if outcome_a else "B"
    outcome_summary = (
        "All repairs remain locally minimal in both neighboring cases. "
        "Repair persistence AND local-minimality preservation confirmed. "
        "Candidate A is substantially weakened in the tested neighboring cases."
        if outcome_a else
        "At least one repair fails local minimality in at least one neighboring case. "
        "This is the first concrete evidence for Candidate A (under restricted local-rationality scope)."
    )

    artifact = {
        "schema_version": "1",
        "generated_at_utc": datetime.now(timezone.utc).isoformat(),
        "date": date_str,
        "experiment": "repair_liftability_step3",
        "step": "Step 3: Local minimality checks",
        "source_triples": _safe_rel(triples_path),
        "source_step2": _safe_rel(step2_path),
        "axiom_family": CANONICAL_FAMILY,
        "scope_note": SCOPE_NOTE,
        "solver": solver,
        "outcome": outcome,
        "outcome_summary": outcome_summary,
        "summary": {
            "n_step2_sat_rows_consumed": len(s2_sat_rows),
            "n_step2_rows_skipped_non_sat": len(s2_skipped),
            "n_element_checks": len(element_rows),
            "n_aggregate_rows": len(aggregate_rows),
            "by_target": by_target,
        },
        "element_rows": element_rows,
        "aggregate_rows": aggregate_rows,
    }
    return artifact


# ── CSV writers ───────────────────────────────────────────────────────────────

ELEM_CSV_FIELDS = [
    "source_case", "target_case",
    "base_package_key", "base_mcs_key",
    "removed_element", "test_package_key",
    "sat_status", "solver", "cnf_path", "manifest_path",
]

AGG_CSV_FIELDS = [
    "source_case", "target_case",
    "base_package_key", "base_mcs_key",
    "repaired_package_key", "base_repair_size",
    "step2_sat_status", "num_element_checks",
    "num_unsat_checks", "num_sat_checks",
    "locally_minimal", "witness_removed_elements_for_failure",
]


def write_csv(path: Path, rows: list[dict[str, Any]], fields: list[str]) -> None:
    with path.open("w", newline="", encoding="utf-8") as f:
        writer = csv.DictWriter(f, fieldnames=fields, extrasaction="ignore")
        writer.writeheader()
        for row in rows:
            flat = {k: (json.dumps(v) if isinstance(v, list) else v) for k, v in row.items()}
            writer.writerow(flat)


# ── markdown summary ──────────────────────────────────────────────────────────

def build_markdown(artifact: dict[str, Any]) -> str:
    s = artifact["summary"]
    by_target = s["by_target"]
    agg_rows = artifact["aggregate_rows"]

    lines: list[str] = [
        "# Step 3: Local Minimality Checks",
        "",
        f"**Generated:** {artifact['generated_at_utc']}  ",
        f"**Solver:** {artifact['solver']}  ",
        f"**Outcome:** {artifact['outcome']} — {artifact['outcome_summary']}",
        "",
        "## Scope note",
        "",
        artifact["scope_note"],
        "",
        "## Summary",
        "",
        "| Item | Count |",
        "|------|-------|",
        f"| Step 2 SAT rows consumed | {s['n_step2_sat_rows_consumed']} |",
        f"| Element-level checks emitted | {s['n_element_checks']} |",
        f"| Aggregate rows emitted | {s['n_aggregate_rows']} |",
        "",
        "### By target case",
        "",
        "| Target | Aggregate rows | Locally minimal | Not locally minimal |",
        "|--------|---------------|-----------------|---------------------|",
    ]
    for tc, counts in by_target.items():
        lines.append(
            f"| `{tc}` | {counts['n_aggregate_rows']} "
            f"| {counts['locally_minimal']} "
            f"| {counts['not_locally_minimal']} |"
        )

    lines += [
        "",
        "## Aggregate result table",
        "",
        "| # | Base package | MCS R | Target | |R| | SAT checks | UNSAT checks | Locally minimal | Witness failures |",
        "|---|-------------|-------|--------|-----|------------|--------------|-----------------|------------------|",
    ]
    for i, row in enumerate(agg_rows, 1):
        lm_str = "✓" if row["locally_minimal"] else "✗"
        wit = ", ".join(row["witness_removed_elements_for_failure"]) or "—"
        lines.append(
            f"| {i} | `{row['base_package_key']}` | `{row['base_mcs_key']}` "
            f"| `{row['target_case']}` | {row['base_repair_size']} "
            f"| {row['num_sat_checks']} | {row['num_unsat_checks']} "
            f"| {lm_str} | {wit} |"
        )

    lines += [
        "",
        "## Element-level checks",
        "",
        "| Base package | MCS R | Target | r removed | Test package | Status |",
        "|-------------|-------|--------|-----------|-------------|--------|",
    ]
    for e in artifact["element_rows"]:
        lines.append(
            f"| `{e['base_package_key']}` | `{e['base_mcs_key']}` "
            f"| `{e['target_case']}` | `{e['removed_element']}` "
            f"| `{e['test_package_key']}` | **{e['sat_status']}** |"
        )

    lines += [
        "",
        "## Interpretation",
        "",
        f"**Outcome {artifact['outcome']}:** {artifact['outcome_summary']}",
        "",
    ]

    if artifact["outcome"] == "A":
        lines += [
            "- All repairs persist (SAT, Step 2) and are locally minimal (Step 3) "
            "in both `(2,5)` and `(3,4)` under the restricted local-rationality family.",
            "- This weakens Candidate A for this family and these neighboring cases.",
            "- Consider pivoting to Candidate B (encoding sensitivity) or introducing a "
            "stronger rationality encoding to extend the experiment.",
        ]
    else:
        non_lm = [r for r in agg_rows if not r["locally_minimal"]]
        lines.append(
            f"- {len(non_lm)} repair(s) fail local minimality in at least one larger case."
        )
        for r in non_lm:
            lines.append(
                f"  - `({r['base_package_key']}, R={r['base_mcs_key']})` "
                f"in `{r['target_case']}`: "
                f"witness failure at removing `{r['witness_removed_elements_for_failure']}`"
            )
        lines += [
            "- These rows are candidate evidence for Candidate A under the restricted "
            "local-rationality scope.",
        ]

    lines += [
        "",
        "All conclusions must be interpreted within the local-rationality family defined by "
        "`no_cycle3` and `no_cycle4`. Do **not** extend claims to full `SocialAcyclic`.",
        "",
        "See `docs/no_cycle_interpretation_note.md` and `docs/axiom_semantics_scaling.md`.",
        "",
    ]
    return "\n".join(lines)


# ── main ──────────────────────────────────────────────────────────────────────

def main() -> None:
    ap = argparse.ArgumentParser(
        description=(
            "Step 3 of the repair-liftability experiment. "
            "For each Step 2 SAT row, checks whether the base repair R is locally "
            "minimal in the larger case by testing A \\ (R \\ {r}) for each r ∈ R."
        )
    )
    ap.add_argument("--triples", type=Path, required=True,
                    help="Path to Step 1 base_triples.json")
    ap.add_argument("--step2", type=Path, required=True,
                    help="Path to Step 2 liftability_step2.json")
    ap.add_argument("--date", type=str, default=None,
                    help="Date label e.g. 20260401. Defaults to today (UTC).")
    ap.add_argument("--outdir", type=Path, default=None,
                    help="Output directory. Defaults to results/<date>/repair_liftability/.")
    ap.add_argument("--solver", type=str, default=DEFAULT_SOLVER,
                    help=f"SAT solver executable (default: {DEFAULT_SOLVER})")
    args = ap.parse_args()

    date_str = args.date or datetime.now(timezone.utc).strftime("%Y%m%d")
    outdir: Path = args.outdir or (REPO_ROOT / "results" / date_str / "repair_liftability")
    for p in (args.triples, args.step2):
        if not p.exists():
            raise FileNotFoundError(f"Required input not found: {p}")

    print(f"Triples: {args.triples}")
    print(f"Step 2:  {args.step2}")
    print(f"Outdir:  {outdir}")
    print(f"Solver:  {args.solver}")
    outdir.mkdir(parents=True, exist_ok=True)

    artifact = run_step3(
        triples_path=args.triples,
        step2_path=args.step2,
        outdir=outdir,
        date_str=date_str,
        solver=args.solver,
    )

    json_path = outdir / "liftability_step3.json"
    elem_csv = outdir / "liftability_step3_element_checks.csv"
    agg_csv  = outdir / "liftability_step3.csv"
    md_path  = outdir / "liftability_step3.md"

    _write_json(json_path, artifact)
    write_csv(elem_csv, artifact["element_rows"], ELEM_CSV_FIELDS)
    write_csv(agg_csv,  artifact["aggregate_rows"], AGG_CSV_FIELDS)
    md_path.write_text(build_markdown(artifact), encoding="utf-8")

    s = artifact["summary"]
    print(f"\nStep 3 complete.  Outcome: {artifact['outcome']}")
    print(f"  Step 2 SAT rows consumed  : {s['n_step2_sat_rows_consumed']}")
    print(f"  Element-level checks      : {s['n_element_checks']}")
    print(f"  Aggregate rows            : {s['n_aggregate_rows']}")
    for tc, c in s["by_target"].items():
        print(f"  {tc}: locally_minimal={c['locally_minimal']}  not={c['not_locally_minimal']}")
    print(f"\n{artifact['outcome_summary']}")
    print(f"\nArtifacts written:")
    print(f"  {json_path}")
    print(f"  {agg_csv}")
    print(f"  {elem_csv}")
    print(f"  {md_path}")


if __name__ == "__main__":
    main()
