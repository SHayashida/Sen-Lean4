#!/usr/bin/env python3
"""
M2.1 Step 0 rerun for the Option D positive track ((2,m) two-witness split).

This is the same Step 0 ≡CM-persistence check as
`scripts/exploration/candidate_b/step0_equiv_check.py`, but the bundled/split
packages are produced by the isolated legacy-style two-voter encoder
`option_d_encoder.py` instead of the parametric `pair_selectors_v1` generator.

Why a separate runner:
  The default Step 0 checker calls the repository generator, whose `auto` mode
  uses `pair_selectors_v1` (Option C machinery) outside (2,4). Option D must use
  the legacy-style two-series split with NO pair-selector variables/clauses, so
  the split package is generable at (2,5) without contaminating the ≡CM test
  with Option C selector logic.

Scope:
  * cases: (2,4) base-case control and (2,5) positive-track family case.
  * n = 2 only; this runner does NOT implement Option C / (3,4).
  * Step 0 only — repair enumeration is NOT authorized.

All ρ construction/verification and classification logic is reused from the
existing Step 0 checker, so the equivalence test is identical; only the encoder
differs.
"""

from __future__ import annotations

import argparse
import json
import sys
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

HERE = Path(__file__).resolve().parent
if str(HERE) not in sys.path:
    sys.path.insert(0, str(HERE))

import option_d_encoder  # noqa: E402
from step0_equiv_check import (  # noqa: E402
    BUNDLED_PACKAGE,
    CLASS_EQUIV_CM,
    CLASS_INCONCLUSIVE,
    CLASS_SAT_EQUIV,
    CLASS_STATUS_DIVERGES,
    SCOPE_STATEMENT,
    TRANSPORT_MAP,
    _package_id,
    _parse_clauses,
    _solve,
    _split_package,
    find_renaming,
)

# (2,4) control + (2,5) Option D positive-track case. No (3,4): that is Option C.
DEFAULT_CASES = [(2, 4), (2, 5)]


def run_case(
    *,
    n: int,
    m: int,
    outdir: Path,
    solver: str,
    max_solve_clauses: int,
    solve_timeout_sec: float,
) -> dict[str, Any]:
    bundled_pkg = BUNDLED_PACKAGE
    split_pkg = _split_package(bundled_pkg)
    case_dir = outdir / f"n{n}_m{m}"
    case_dir.mkdir(parents=True, exist_ok=True)

    report: dict[str, Any] = {
        "case": {"n": n, "m": m},
        "track": "option_d_positive",
        "encoder": option_d_encoder.ENCODING_LABEL,
        "uses_pair_selectors": False,
        "base_case_control": (n, m) == (2, 4),
        "bundled_package": _package_id(bundled_pkg),
        "split_package": _package_id(split_pkg),
        "transport_map": {k: list(v) for k, v in TRANSPORT_MAP.items()},
        "bundled_var_count": None,
        "split_var_count": None,
        "bundled_clause_count": None,
        "split_clause_count": None,
        "bundled_status": None,
        "split_status": None,
        "clause_multiset_equivalence": {"verified": False, "method": "none", "reason": "not evaluated"},
        "classification": CLASS_INCONCLUSIVE,
        "explanation": "",
        "local_rationality_scope": SCOPE_STATEMENT,
    }

    # 1-2. Generate bundled and split packages with the Option D encoder.
    try:
        bundled = option_d_encoder.generate_package(
            n=n, m=m, axiom_names=bundled_pkg, out_path=case_dir / "bundled.cnf", manifest_path=case_dir / "bundled.manifest.json"
        )
        split = option_d_encoder.generate_package(
            n=n, m=m, axiom_names=split_pkg, out_path=case_dir / "split.cnf", manifest_path=case_dir / "split.manifest.json"
        )
    except Exception as exc:  # noqa: BLE001 - exploratory; record precise reason
        report["classification"] = CLASS_INCONCLUSIVE
        report["explanation"] = f"Option D generation failed: {type(exc).__name__}: {exc}"
        return report

    report["bundled_var_count"] = bundled["nvars"]
    report["bundled_clause_count"] = bundled["nclauses"]
    report["split_var_count"] = split["nvars"]
    report["split_clause_count"] = split["nclauses"]
    report["bundled_per_lever_clause_counts"] = bundled["per_lever_clause_counts"]
    report["split_per_lever_clause_counts"] = split["per_lever_clause_counts"]

    # 3. Parse clause multisets.
    try:
        bundled_clauses = _parse_clauses(bundled["cnf"])
        split_clauses = _parse_clauses(split["cnf"])
    except Exception as exc:  # noqa: BLE001
        report["classification"] = CLASS_INCONCLUSIVE
        report["explanation"] = f"clause parsing failed: {type(exc).__name__}: {exc}"
        return report

    # 4. SAT/UNSAT status (Option D CNFs are small/fast to solve).
    if bundled["nclauses"] <= max_solve_clauses:
        b_solve = _solve(bundled["cnf"], solver, solve_timeout_sec)
        report["bundled_status"] = b_solve["status"]
        report["bundled_status_detail"] = b_solve["detail"]
    else:
        report["bundled_status_detail"] = f"not solved: {bundled['nclauses']} clauses exceed budget {max_solve_clauses}"
    if split["nclauses"] <= max_solve_clauses:
        s_solve = _solve(split["cnf"], solver, solve_timeout_sec)
        report["split_status"] = s_solve["status"]
        report["split_status_detail"] = s_solve["detail"]
    else:
        report["split_status_detail"] = f"not solved: {split['nclauses']} clauses exceed budget {max_solve_clauses}"

    # 5. Construct and verify ρ, then classify (identical logic to base checker).
    rho_result = find_renaming(bundled_clauses, split_clauses)
    report["clause_multiset_equivalence"] = {
        "verified": bool(rho_result["verified"]),
        "method": rho_result["method"],
        "reason": rho_result["reason"],
    }

    b_status = report["bundled_status"]
    s_status = report["split_status"]
    status_known = b_status in {"SAT", "UNSAT"} and s_status in {"SAT", "UNSAT"}

    if status_known and b_status != s_status:
        report["classification"] = CLASS_STATUS_DIVERGES
        report["explanation"] = (
            f"bundled status {b_status} differs from split status {s_status}."
        )
        return report

    if not status_known:
        report["classification"] = CLASS_INCONCLUSIVE
        report["explanation"] = (
            "SAT/UNSAT status could not be established for both packages "
            f"(bundled={b_status}, split={s_status}); status agreement is required "
            "before ≡CM persistence may be asserted."
        )
        return report

    if rho_result["verified"]:
        report["classification"] = CLASS_EQUIV_CM
        note = (
            f"status agrees ({b_status}) and a variable-renaming bijection ρ was "
            f"constructed and verified ({rho_result['method']}): the Option D "
            "legacy-style two-series split has bundled and split clause multisets "
            "that coincide under ρ, with no pair-selector variables or clauses "
            "introduced, so ≡CM persists for this case."
        )
        if (n, m) == (2, 5):
            note += (
                " This is for the (2,m) positive track only; it does NOT settle the "
                "Option C / voter-dimension boundary track (n>2, e.g. (3,4))."
            )
        report["explanation"] = note
    else:
        report["classification"] = CLASS_SAT_EQUIV
        report["explanation"] = (
            f"status agrees ({b_status}) but no variable-renaming bijection ρ could "
            f"be verified ({rho_result['reason']}). NOTE: the Option D encoder "
            "introduces no pair-selector variables/clauses (uses_pair_selectors="
            "False), so any ≡CM failure here is NOT attributable to pair-selector "
            "machinery; inspect the per-lever clause counts before drawing a boundary "
            "conclusion."
        )
    return report


def _summary_md(payload: dict[str, Any]) -> str:
    lines = [
        "# M2.1 Step 0 — Option D positive track (≡CM persistence)",
        "",
        f"**Generated:** {payload['generated_at_utc']}  ",
        f"**Encoder:** `{payload['encoder']}` (no pair selectors)  ",
        f"**Scope:** {payload['local_rationality_scope']}",
        "",
        "Step 0 only. Repair enumeration is NOT authorized. Option C / (3,4) is not implemented.",
        "",
        "| case | classification | bundled (vars/clauses) | split (vars/clauses) | ≡CM verified |",
        "| --- | --- | --- | --- | --- |",
    ]
    for r in payload["cases"]:
        c = r["case"]
        b = f"{r['bundled_var_count']}/{r['bundled_clause_count']}"
        s = f"{r['split_var_count']}/{r['split_clause_count']}"
        lines.append(
            f"| ({c['n']},{c['m']}) | `{r['classification']}` | {b} | {s} | "
            f"{r['clause_multiset_equivalence']['verified']} |"
        )
    lines.append("")
    for r in payload["cases"]:
        c = r["case"]
        lines.append(f"## ({c['n']},{c['m']}) — `{r['classification']}`")
        lines.append("")
        lines.append(r["explanation"])
        lines.append("")
    return "\n".join(lines).rstrip() + "\n"


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--outdir", type=Path, default=Path("/tmp/candidate_b_step0_option_d"))
    ap.add_argument("--cases", type=str, default=",".join(f"{n}:{m}" for n, m in DEFAULT_CASES))
    ap.add_argument("--solver", type=str, default="cadical")
    ap.add_argument("--max-solve-clauses", type=int, default=8_000_000, help="Option D CNFs solve quickly; default high enough for (2,5).")
    ap.add_argument("--solve-timeout-sec", type=float, default=300.0)
    args = ap.parse_args()

    cases: list[tuple[int, int]] = []
    for token in args.cases.split(","):
        token = token.strip()
        if not token:
            continue
        n_str, m_str = token.split(":")
        cases.append((int(n_str), int(m_str)))

    outdir = args.outdir
    outdir.mkdir(parents=True, exist_ok=True)

    case_reports = [
        run_case(
            n=n,
            m=m,
            outdir=outdir,
            solver=args.solver,
            max_solve_clauses=args.max_solve_clauses,
            solve_timeout_sec=args.solve_timeout_sec,
        )
        for (n, m) in cases
    ]

    payload = {
        "experiment": "m2.1_step0_option_d_equiv_cm_persistence",
        "track": "option_d_positive",
        "encoder": option_d_encoder.ENCODING_LABEL,
        "uses_pair_selectors": False,
        "generated_at_utc": datetime.now(timezone.utc).isoformat(),
        "step": "Step 0 (≡CM persistence) only — repair enumeration not authorized",
        "transport_map": {k: list(v) for k, v in TRANSPORT_MAP.items()},
        "transport_map_note": (
            "π is a lever correspondence / repair-transport map, not a semantic "
            "equivalence claim between axiom formulas."
        ),
        "bundled_package": _package_id(BUNDLED_PACKAGE),
        "split_package": _package_id(_split_package(BUNDLED_PACKAGE)),
        "local_rationality_scope": SCOPE_STATEMENT,
        "option_c_status": "not implemented; (3,4) voter-dimension boundary track remains open",
        "cases": case_reports,
    }

    report_path = outdir / "step0_option_d_comparison.json"
    report_path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    summary_path = outdir / "step0_option_d_summary.md"
    summary_path.write_text(_summary_md(payload), encoding="utf-8")

    print(f"Wrote {report_path}")
    print(f"Wrote {summary_path}")
    for r in case_reports:
        c = r["case"]
        print(f"  ({c['n']},{c['m']}): {r['classification']}")
    print("Step 0 only — repair enumeration is NOT authorized; Option C / (3,4) not implemented.")


if __name__ == "__main__":
    main()
