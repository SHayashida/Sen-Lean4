#!/usr/bin/env python3
"""Step 2: Apply each base-case repair to larger cases (n=2,m=5) and (n=3,m=4).

Reads base_triples.json produced by Step 1, generates a CNF for each
(repaired_package, target_case) pair, solves it, and records SAT/UNSAT.

Usage (from repo root):
    python3 scripts/run_repair_liftability_step2.py \\
        --triples results/20260401/repair_liftability/base_triples.json \\
        --date 20260401 \\
        --outdir results/20260401/repair_liftability

See docs/experiment_protocol_repair_liftability.md for Step 2 specification.
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

TARGET_CASES: list[dict[str, int]] = [
    {"n": 2, "m": 5, "label": "n2_m5"},
    {"n": 3, "m": 4, "label": "n3_m4"},
]

SCOPE_NOTE = (
    "no_cycle3 and no_cycle4 are treated as local-rationality approximations, "
    "not full SocialAcyclic. Results for (2,5) are valid only within that "
    "restricted local-rationality family. "
    "See docs/no_cycle_interpretation_note.md and docs/axiom_semantics_scaling.md."
)

DEFAULT_SOLVER = "cadical"

# ── helpers ───────────────────────────────────────────────────────────────────


def _load_json(path: Path) -> Any:
    return json.loads(path.read_text(encoding="utf-8"))


def _write_json(path: Path, payload: Any) -> None:
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


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


def _safe_rel(path: Path) -> str:
    """Return path relative to repo root, or absolute string if not under it."""
    try:
        return str(path.relative_to(REPO_ROOT))
    except ValueError:
        return str(path)


# ── SAT solver call ───────────────────────────────────────────────────────────


def _solve(
    cnf_path: Path,
    *,
    solver: str,
    log_path: Path,
) -> tuple[str, float]:
    """Run solver on cnf_path, write log, return (status, duration_sec)."""
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
            log_path,
            cmd=cmd,
            return_code=proc.returncode,
            stdout=proc.stdout,
            stderr=proc.stderr,
            duration_sec=duration,
        )
    except FileNotFoundError as ex:
        duration = time.perf_counter() - t0
        status = "UNKNOWN"
        _write_solver_log(
            log_path,
            cmd=cmd,
            return_code=None,
            stdout="",
            stderr="",
            duration_sec=duration,
            error=str(ex),
        )
    return status, duration


# ── core builder ─────────────────────────────────────────────────────────────


def run_step2(
    *,
    triples_path: Path,
    outdir: Path,
    date_str: str,
    solver: str,
) -> dict[str, Any]:
    triples_doc = _load_json(triples_path)
    triples: list[dict[str, Any]] = triples_doc["triples"]
    n_step1 = len(triples)

    # subdirectory for generated CNFs / manifests / logs
    cnf_root = outdir / "step2_cnfs"

    rows: list[dict[str, Any]] = []
    seen_keys: set[tuple[str, str, str]] = set()

    for triple in triples:
        base_pkg = triple["base_package"]
        base_pkg_key: str = triple["base_package_key"]
        base_mcs = triple["base_mcs"]
        base_mcs_key: str = triple["base_mcs_key"]
        repaired_pkg: list[str] = triple["repaired_package"]
        repaired_pkg_key: str = triple["repaired_package_key"]

        for tc in TARGET_CASES:
            n, m, label = tc["n"], tc["m"], tc["label"]
            dedup = (base_pkg_key, base_mcs_key, label)
            if dedup in seen_keys:
                raise RuntimeError(f"Duplicate row: {dedup}")
            seen_keys.add(dedup)

            # safe filename from repaired_package_key
            safe_key = repaired_pkg_key.replace("+", "_")
            case_dir = cnf_root / label / safe_key
            case_dir.mkdir(parents=True, exist_ok=True)

            cnf_path = case_dir / "repaired.cnf"
            manifest_path = case_dir / "repaired.manifest.json"
            log_path = case_dir / "solver.log"

            # generate CNF for (n, m) with repaired_package axioms
            run_generation(
                n=n,
                m=m,
                axiom_names=repaired_pkg,
                out_path=cnf_path,
                manifest_path=manifest_path,
            )

            # solve
            sat_status, duration_sec = _solve(cnf_path, solver=solver, log_path=log_path)
            if sat_status not in {"SAT", "UNSAT"}:
                raise RuntimeError(
                    f"Solver returned non-decisive status '{sat_status}' for "
                    f"repaired_pkg={repaired_pkg_key} target={label}. "
                    "Check that the solver is installed and accessible."
                )

            rows.append({
                "source_case": "n2_m4",
                "target_case": label,
                "n_target": n,
                "m_target": m,
                "axiom_family": CANONICAL_FAMILY,
                "base_package": base_pkg,
                "base_package_key": base_pkg_key,
                "base_mcs": base_mcs,
                "base_mcs_key": base_mcs_key,
                "repaired_package": repaired_pkg,
                "repaired_package_key": repaired_pkg_key,
                "sat_status": sat_status,
                "solver": solver,
                "duration_sec": round(duration_sec, 6),
                "cnf_path": _safe_rel(cnf_path),
                "manifest_path": _safe_rel(manifest_path),
                "solver_log_path": _safe_rel(log_path),
                "notes": SCOPE_NOTE,
            })

    # ── validation ──────────────────────────────────────────────────────────
    expected_rows = n_step1 * len(TARGET_CASES)
    if len(rows) != expected_rows:
        raise RuntimeError(
            f"Expected {expected_rows} rows ({n_step1} triples × {len(TARGET_CASES)} target cases), "
            f"got {len(rows)}."
        )
    # every row has sat_status
    missing = [r["repaired_package_key"] for r in rows if r["sat_status"] not in {"SAT", "UNSAT"}]
    if missing:
        raise RuntimeError(f"Rows missing decisive SAT/UNSAT: {missing}")
    # no duplicate (base_package_key, base_mcs_key, target_case)
    row_keys = [(r["base_package_key"], r["base_mcs_key"], r["target_case"]) for r in rows]
    if len(row_keys) != len(set(row_keys)):
        raise RuntimeError("Duplicate (base_package_key, base_mcs_key, target_case) rows detected.")

    # ── summary stats ────────────────────────────────────────────────────────
    by_target: dict[str, dict[str, int]] = {}
    for tc in TARGET_CASES:
        label = tc["label"]
        tc_rows = [r for r in rows if r["target_case"] == label]
        by_target[label] = {
            "total": len(tc_rows),
            "SAT": sum(1 for r in tc_rows if r["sat_status"] == "SAT"),
            "UNSAT": sum(1 for r in tc_rows if r["sat_status"] == "UNSAT"),
        }

    artifact = {
        "schema_version": "1",
        "generated_at_utc": datetime.now(timezone.utc).isoformat(),
        "date": date_str,
        "experiment": "repair_liftability_step2",
        "step": "Step 2: Apply each repair to larger cases",
        "source_triples": _safe_rel(triples_path),
        "axiom_family": CANONICAL_FAMILY,
        "scope_note": SCOPE_NOTE,
        "solver": solver,
        "summary": {
            "n_step1_triples_consumed": n_step1,
            "n_step2_rows_emitted": len(rows),
            "target_cases": [tc["label"] for tc in TARGET_CASES],
            "by_target": by_target,
        },
        "rows": rows,
    }
    return artifact


# ── CSV writer ────────────────────────────────────────────────────────────────

CSV_FIELDS = [
    "source_case",
    "target_case",
    "base_package_key",
    "base_mcs_key",
    "repaired_package_key",
    "sat_status",
    "solver",
    "duration_sec",
    "cnf_path",
    "manifest_path",
]


def write_csv(path: Path, rows: list[dict[str, Any]]) -> None:
    with path.open("w", newline="", encoding="utf-8") as f:
        writer = csv.DictWriter(f, fieldnames=CSV_FIELDS, extrasaction="ignore")
        writer.writeheader()
        writer.writerows(rows)


# ── markdown summary ──────────────────────────────────────────────────────────

def build_markdown(artifact: dict[str, Any]) -> str:
    s = artifact["summary"]
    by_target = s["by_target"]
    rows = artifact["rows"]

    # build pivot: repaired_package_key × target_case → sat_status
    pivot: dict[tuple[str, str, str], str] = {}
    for r in rows:
        pivot[(r["base_package_key"], r["base_mcs_key"], r["target_case"])] = r["sat_status"]

    lines: list[str] = [
        "# Step 2: Repair Liftability — Apply Repairs to Larger Cases",
        "",
        f"**Generated:** {artifact['generated_at_utc']}  ",
        f"**Source triples:** `{artifact['source_triples']}`  ",
        f"**Solver:** {artifact['solver']}  ",
        "",
        "## Scope note",
        "",
        artifact["scope_note"],
        "",
        "## Summary",
        "",
        "| Item | Count |",
        "|------|-------|",
        f"| Step 1 triples consumed | {s['n_step1_triples_consumed']} |",
        f"| Step 2 rows emitted | {s['n_step2_rows_emitted']} |",
        "",
        "### By target case",
        "",
        "| Target | Total | SAT | UNSAT |",
        "|--------|-------|-----|-------|",
    ]
    for label, counts in by_target.items():
        lines.append(f"| `{label}` | {counts['total']} | {counts['SAT']} | {counts['UNSAT']} |")

    lines += [
        "",
        "## Result table",
        "",
        "| # | Base package | MCS R_i | Repaired A\\\\R_i | (2,5) | (3,4) |",
        "|---|-------------|---------|----------------|-------|-------|",
    ]

    # collect unique triples in order
    seen: list[tuple[str, str, str]] = []
    seen_set: set[tuple[str, str, str]] = set()
    for r in rows:
        k = (r["base_package_key"], r["base_mcs_key"], r["repaired_package_key"])
        if k not in seen_set:
            seen.append(k)
            seen_set.add(k)

    for i, (bpk, mcs_k, rpk) in enumerate(seen, 1):
        s25 = pivot.get((bpk, mcs_k, "n2_m5"), "—")
        s34 = pivot.get((bpk, mcs_k, "n3_m4"), "—")
        lines.append(f"| {i} | `{bpk}` | `{mcs_k}` | `{rpk}` | {s25} | {s34} |")

    lines += [
        "",
        "## Interpretation",
        "",
        "- **SAT** in a larger case: the repair persists. Proceed to Step 3 to check local minimality.",
        "- **UNSAT** in a larger case: strong non-liftability for this repair in this family size.",
        "",
        "All results must be interpreted within the local-rationality family defined by "
        "`no_cycle3` and `no_cycle4`. Do **not** extend claims to full `SocialAcyclic` "
        "unless a stronger rationality encoding is introduced in later work.",
        "",
        "See `docs/no_cycle_interpretation_note.md` and `docs/axiom_semantics_scaling.md`.",
        "",
    ]
    return "\n".join(lines)


# ── main ──────────────────────────────────────────────────────────────────────

def main() -> None:
    ap = argparse.ArgumentParser(
        description=(
            "Step 2 of the repair-liftability experiment. "
            "Reads Step 1 base_triples.json, generates CNF for each repaired package "
            "at (2,5) and (3,4), solves, and writes liftability_step2.{json,csv,md}."
        )
    )
    ap.add_argument(
        "--triples",
        type=Path,
        required=True,
        help="Path to Step 1 base_triples.json",
    )
    ap.add_argument(
        "--date",
        type=str,
        default=None,
        help="Date label for the run, e.g. 20260401. Defaults to today (UTC).",
    )
    ap.add_argument(
        "--outdir",
        type=Path,
        default=None,
        help="Output directory. Defaults to results/<date>/repair_liftability/.",
    )
    ap.add_argument(
        "--solver",
        type=str,
        default=DEFAULT_SOLVER,
        help=f"SAT solver executable (default: {DEFAULT_SOLVER})",
    )
    args = ap.parse_args()

    date_str = args.date or datetime.now(timezone.utc).strftime("%Y%m%d")
    outdir: Path = args.outdir if args.outdir is not None else (
        REPO_ROOT / "results" / date_str / "repair_liftability"
    )
    triples_path: Path = args.triples
    if not triples_path.exists():
        raise FileNotFoundError(f"base_triples.json not found: {triples_path}")

    print(f"Triples:  {triples_path}")
    print(f"Outdir:   {outdir}")
    print(f"Solver:   {args.solver}")
    outdir.mkdir(parents=True, exist_ok=True)

    artifact = run_step2(
        triples_path=triples_path,
        outdir=outdir,
        date_str=date_str,
        solver=args.solver,
    )

    json_path = outdir / "liftability_step2.json"
    csv_path = outdir / "liftability_step2.csv"
    md_path = outdir / "liftability_step2.md"

    _write_json(json_path, artifact)
    write_csv(csv_path, artifact["rows"])
    md_path.write_text(build_markdown(artifact), encoding="utf-8")

    s = artifact["summary"]
    print(f"\nStep 2 complete.")
    print(f"  Step 1 triples consumed : {s['n_step1_triples_consumed']}")
    print(f"  Step 2 rows emitted     : {s['n_step2_rows_emitted']}")
    for label, counts in s["by_target"].items():
        print(f"  {label}: SAT={counts['SAT']}  UNSAT={counts['UNSAT']}")
    print(f"\nArtifacts written:")
    print(f"  {json_path}")
    print(f"  {csv_path}")
    print(f"  {md_path}")


if __name__ == "__main__":
    main()
