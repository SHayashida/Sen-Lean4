#!/usr/bin/env python3
"""
M2.1 Step 0 — exploratory clause-multiset-equivalence (≡CM) persistence checker.

Purpose
-------
Step 0 of M2.1 asks a single, narrow question before any repair enumeration:

    Does the M1.5 bundled/split clause-multiset-equivalence (≡CM) structure
    persist at larger finite cases under the repair-transport map π?

This script is an *exploratory* checker. It does NOT enumerate repairs and it
does NOT compute MCS sets. It only:

  1. generates the bundled package CNF for a case (n, m),
  2. generates the split package CNF (the π-image of the bundled package),
  3. parses both clause multisets,
  4. attempts to *construct and verify* a variable-renaming bijection ρ under
     which the bundled and split clause multisets coincide (M1.5 Definition-2
     sense), and
  5. classifies the case.

Discipline (must be preserved)
------------------------------
* ≡CM (`equiv_cm_persists`) is asserted ONLY when a renaming bijection ρ is
  actually constructed and re-verified. Equal variable counts and equal clause
  counts are necessary but NOT sufficient and never, on their own, yield
  `equiv_cm_persists`.
* The transport map π is a lever correspondence / repair-transport map. It is
  NOT a claim of semantic equivalence between axiom formulas.
* `no_cycle3 ∧ no_cycle4` is a local-rationality family and is not full
  SocialAcyclic at family scale.
* This is Step 0 only. Repair enumeration remains unauthorized until Step 0 is
  reviewed.

Outputs are written to a temp/local path (default /tmp/candidate_b_step0), never
into tracked results/ paths.
"""

from __future__ import annotations

import argparse
import json
import shutil
import subprocess
import sys
import time
from collections import Counter
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

# Reuse the existing leverized generator; do not add a new generator.
SCRIPTS_DIR = Path(__file__).resolve().parents[2]  # repo/scripts
REPO_ROOT = SCRIPTS_DIR.parent
if str(SCRIPTS_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPTS_DIR))

from gen_dimacs import run_generation  # noqa: E402

# The bundled package and the explicit repair-transport map π.
BUNDLED_PACKAGE = ["asymm", "un", "minlib", "no_cycle3", "no_cycle4"]
TRANSPORT_MAP = {
    "minlib": ["decisive_voter0", "decisive_voter1"],
    "asymm": ["asymm"],
    "un": ["un"],
    "no_cycle3": ["no_cycle3"],
    "no_cycle4": ["no_cycle4"],
}

SCOPE_STATEMENT = (
    "no_cycle3 ∧ no_cycle4 is treated as a local-rationality family and is not "
    "full SocialAcyclic at family scale."
)

# (2,4) is the M1.5 base case; it is included as a ≡CM-positive control that
# exercises the ρ-construction machinery. The M2.1 targets are (2,5) and (3,4).
DEFAULT_CASES = [(2, 4), (2, 5), (3, 4)]

CLASS_EQUIV_CM = "equiv_cm_persists"
CLASS_SAT_EQUIV = "sat_equiv_only"
CLASS_STATUS_DIVERGES = "status_diverges"
CLASS_INCONCLUSIVE = "inconclusive"


def _split_package(bundled: list[str]) -> list[str]:
    out: list[str] = []
    for lever in bundled:
        out.extend(TRANSPORT_MAP[lever])
    return out


def _package_id(axioms: list[str]) -> str:
    return "+".join(axioms) if axioms else "(empty)"


def _parse_clauses(path: Path) -> list[tuple[int, ...]]:
    clauses: list[tuple[int, ...]] = []
    for raw in path.read_text(encoding="utf-8").splitlines():
        line = raw.strip()
        if not line or line.startswith("c") or line.startswith("p "):
            continue
        parts = [int(x) for x in line.split()]
        if not parts or parts[-1] != 0:
            raise ValueError(f"malformed DIMACS clause line in {path}: {raw!r}")
        clauses.append(tuple(sorted(parts[:-1], key=lambda lit: (abs(lit), lit))))
    return clauses


def _clause_multiset(clauses: list[tuple[int, ...]]) -> Counter[tuple[int, ...]]:
    return Counter(clauses)


def _variables(clauses: list[tuple[int, ...]]) -> set[int]:
    return {abs(lit) for clause in clauses for lit in clause}


def _apply_rho(clauses: list[tuple[int, ...]], rho: dict[int, int]) -> Counter[tuple[int, ...]]:
    out: Counter[tuple[int, ...]] = Counter()
    for clause in clauses:
        mapped = tuple(
            sorted(
                ((1 if lit > 0 else -1) * rho[abs(lit)] for lit in clause),
                key=lambda lit: (abs(lit), lit),
            )
        )
        out[mapped] += 1
    return out


def _verify_rho(
    bundled: list[tuple[int, ...]],
    split_ms: Counter[tuple[int, ...]],
    rho: dict[int, int],
) -> bool:
    return _apply_rho(bundled, rho) == split_ms


def _var_signature(clauses: list[tuple[int, ...]]) -> dict[int, tuple[Any, ...]]:
    """A renaming-invariant per-variable signature for pruning ρ candidates.

    Signature captures, per variable, the multiset of (clause_length, sign)
    incidences. A valid ρ must map variables with equal signatures to each other.
    """
    pos: Counter[int] = Counter()
    neg: Counter[int] = Counter()
    lenpos: dict[int, Counter[int]] = {}
    lenneg: dict[int, Counter[int]] = {}
    for clause in clauses:
        clen = len(clause)
        for lit in clause:
            v = abs(lit)
            if lit > 0:
                pos[v] += 1
                lenpos.setdefault(v, Counter())[clen] += 1
            else:
                neg[v] += 1
                lenneg.setdefault(v, Counter())[clen] += 1
    sig: dict[int, tuple[Any, ...]] = {}
    for v in _variables(clauses):
        sig[v] = (
            pos[v],
            neg[v],
            tuple(sorted(lenpos.get(v, Counter()).items())),
            tuple(sorted(lenneg.get(v, Counter()).items())),
        )
    return sig


def find_renaming(
    bundled: list[tuple[int, ...]],
    split: list[tuple[int, ...]],
    *,
    node_budget: int = 200_000,
) -> dict[str, Any]:
    """Construct and verify a variable-renaming bijection ρ (best effort).

    Returns a dict describing whether a verified ρ exists. ``verified`` is True
    only when a full bijection has been built AND re-verified by applying it.
    Cardinality agreement alone never sets ``verified``.
    """
    b_ms = _clause_multiset(bundled)
    s_ms = _clause_multiset(split)

    # Cheap necessary conditions (necessary, NOT sufficient).
    if len(bundled) != len(split):
        return {"verified": False, "method": "none", "reason": "clause counts differ"}
    if Counter(len(c) for c in bundled) != Counter(len(c) for c in split):
        return {"verified": False, "method": "none", "reason": "clause-length multisets differ"}
    b_vars = _variables(bundled)
    s_vars = _variables(split)
    if len(b_vars) != len(s_vars):
        return {"verified": False, "method": "none", "reason": "distinct-variable counts differ"}

    # Try the identity renaming first (this is the M1.5 base-case situation,
    # where the legacy encoder aligns bundled minlib and split decisive levers).
    if b_vars == s_vars and b_ms == s_ms:
        return {"verified": True, "method": "identity", "reason": "identity renaming verified"}

    # Signature-pruned backtracking fallback.
    b_sig = _var_signature(bundled)
    s_sig = _var_signature(split)
    if Counter(b_sig.values()) != Counter(s_sig.values()):
        return {
            "verified": False,
            "method": "none",
            "reason": "variable signature multisets differ; no renaming can exist",
        }

    candidates: dict[int, list[int]] = {}
    by_sig_s: dict[tuple[Any, ...], list[int]] = {}
    for v, sg in s_sig.items():
        by_sig_s.setdefault(sg, []).append(v)
    for v in sorted(b_vars):
        candidates[v] = list(by_sig_s.get(b_sig[v], []))
        if not candidates[v]:
            return {
                "verified": False,
                "method": "none",
                "reason": f"no signature-compatible split variable for bundled var {v}",
            }

    order = sorted(b_vars, key=lambda v: len(candidates[v]))
    rho: dict[int, int] = {}
    used: set[int] = set()
    nodes = 0
    budget_hit = False

    def backtrack(i: int) -> bool:
        nonlocal nodes, budget_hit
        if i == len(order):
            return _verify_rho(bundled, s_ms, rho)
        v = order[i]
        for w in candidates[v]:
            if w in used:
                continue
            nodes += 1
            if nodes > node_budget:
                budget_hit = True
                return False
            rho[v] = w
            used.add(w)
            if backtrack(i + 1):
                return True
            used.discard(w)
            del rho[v]
            if budget_hit:
                return False
        return False

    if backtrack(0) and _verify_rho(bundled, s_ms, rho):
        return {"verified": True, "method": "backtracking", "reason": "renaming bijection verified"}
    if budget_hit:
        return {
            "verified": False,
            "method": "none",
            "reason": f"backtracking node budget ({node_budget}) exhausted without a verified ρ",
        }
    return {"verified": False, "method": "none", "reason": "no consistent renaming bijection found"}


def _solve(cnf_path: Path, solver: str, timeout_sec: float) -> dict[str, Any]:
    solver_path = shutil.which(solver)
    if solver_path is None:
        return {"status": None, "detail": f"solver '{solver}' not on PATH"}
    try:
        proc = subprocess.run(
            [solver, str(cnf_path)],
            capture_output=True,
            text=True,
            check=False,
            timeout=timeout_sec,
        )
    except subprocess.TimeoutExpired:
        return {"status": None, "detail": f"solver timed out after {timeout_sec}s"}
    if proc.returncode == 10:
        return {"status": "SAT", "detail": "rc=10"}
    if proc.returncode == 20:
        return {"status": "UNSAT", "detail": "rc=20"}
    text = f"{proc.stdout}\n{proc.stderr}".upper()
    if "UNSATISFIABLE" in text:
        return {"status": "UNSAT", "detail": "stdout"}
    if "SATISFIABLE" in text:
        return {"status": "SAT", "detail": "stdout"}
    return {"status": None, "detail": f"unrecognized solver output (rc={proc.returncode})"}


def _generate(n: int, m: int, axioms: list[str], outdir: Path, label: str) -> dict[str, Any]:
    cnf = outdir / f"{label}.cnf"
    manifest = outdir / f"{label}.manifest.json"
    mf = run_generation(
        n=n,
        m=m,
        axiom_names=axioms,
        out_path=cnf,
        manifest_path=manifest,
    )
    return {
        "cnf": cnf,
        "nvars": int(mf["nvars"]),
        "nclauses": int(mf["nclauses"]),
        "encoding": mf.get("encoding"),
    }


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
        "clause_multiset_equivalence": {
            "verified": False,
            "method": "none",
            "reason": "not evaluated",
        },
        "classification": CLASS_INCONCLUSIVE,
        "explanation": "",
        "local_rationality_scope": SCOPE_STATEMENT,
    }

    # 1. Generate bundled package.
    try:
        bundled = _generate(n, m, bundled_pkg, case_dir, "bundled")
    except Exception as exc:  # noqa: BLE001 - exploratory; record precise reason
        report["classification"] = CLASS_INCONCLUSIVE
        report["explanation"] = (
            f"bundled package generation failed: {type(exc).__name__}: {exc}"
        )
        return report
    report["bundled_var_count"] = bundled["nvars"]
    report["bundled_clause_count"] = bundled["nclauses"]
    report["bundled_encoding"] = bundled["encoding"]

    # 2. Generate split package (π-image). This is where family-scale Step 0
    #    currently stops: the split levers are Sen24-only in the present encoder.
    try:
        split = _generate(n, m, split_pkg, case_dir, "split")
    except Exception as exc:  # noqa: BLE001 - record the precise generator limit
        report["classification"] = CLASS_INCONCLUSIVE
        report["clause_multiset_equivalence"] = {
            "verified": False,
            "method": "none",
            "reason": "split package not generated; ≡CM not evaluable",
        }
        report["explanation"] = (
            f"split package generation failed: {type(exc).__name__}: {exc}. "
            "The transport-map split image {decisive_voter0, decisive_voter1} is "
            "encoded only in legacy selectors_v1 mode, which is restricted to the "
            "Sen24 base case (2,4); no family-scale parametric split encoding "
            "exists in the current generator interface. Per the additional "
            "constraint, this two-lever split image may also be structurally "
            "insufficient once the voter count exceeds two, e.g. at (3,4). "
            "Recorded as a transport-map / generator-interface scope finding, "
            "not a checker failure."
        )
        return report
    report["split_var_count"] = split["nvars"]
    report["split_clause_count"] = split["nclauses"]
    report["split_encoding"] = split["encoding"]

    # 3. Parse clause multisets.
    try:
        bundled_clauses = _parse_clauses(bundled["cnf"])
        split_clauses = _parse_clauses(split["cnf"])
    except Exception as exc:  # noqa: BLE001
        report["classification"] = CLASS_INCONCLUSIVE
        report["explanation"] = f"clause parsing failed: {type(exc).__name__}: {exc}"
        return report

    # 4. Optionally determine SAT/UNSAT status (guarded by clause-count budget).
    if bundled["nclauses"] <= max_solve_clauses:
        b_solve = _solve(bundled["cnf"], solver, solve_timeout_sec)
        report["bundled_status"] = b_solve["status"]
        report["bundled_status_detail"] = b_solve["detail"]
    else:
        report["bundled_status_detail"] = (
            f"not solved: {bundled['nclauses']} clauses exceed budget {max_solve_clauses}"
        )
    if split["nclauses"] <= max_solve_clauses:
        s_solve = _solve(split["cnf"], solver, solve_timeout_sec)
        report["split_status"] = s_solve["status"]
        report["split_status_detail"] = s_solve["detail"]
    else:
        report["split_status_detail"] = (
            f"not solved: {split['nclauses']} clauses exceed budget {max_solve_clauses}"
        )

    # 5. Construct and verify ρ, then classify.
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
            f"bundled status {b_status} differs from split status {s_status}; "
            "the transferred package does not even agree on satisfiability status."
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

    # status agrees from here on.
    if rho_result["verified"]:
        report["classification"] = CLASS_EQUIV_CM
        report["explanation"] = (
            f"status agrees ({b_status}) and a variable-renaming bijection ρ was "
            f"constructed and verified ({rho_result['method']}): the bundled and "
            "split clause multisets coincide under ρ, so ≡CM persists for this case."
        )
    else:
        report["classification"] = CLASS_SAT_EQUIV
        report["explanation"] = (
            f"status agrees ({b_status}) but no variable-renaming bijection ρ could "
            f"be verified ({rho_result['reason']}); cardinality agreement alone is "
            "insufficient for ≡CM, so this is satisfiability-equivalence only and "
            "the M1.5 clause-multiset-equivalence shield does not transfer here."
        )
    return report


def _summary_md(payload: dict[str, Any]) -> str:
    lines = [
        "# M2.1 Step 0 — ≡CM persistence report",
        "",
        f"**Generated:** {payload['generated_at_utc']}  ",
        f"**Scope:** {payload['local_rationality_scope']}",
        "",
        "Step 0 only. Repair enumeration is NOT authorized until Step 0 is reviewed.",
        "",
        "| case | classification | bundled (vars/clauses) | split (vars/clauses) | ≡CM verified |",
        "| --- | --- | --- | --- | --- |",
    ]
    for r in payload["cases"]:
        c = r["case"]
        b = f"{r['bundled_var_count']}/{r['bundled_clause_count']}"
        s = (
            f"{r['split_var_count']}/{r['split_clause_count']}"
            if r["split_var_count"] is not None
            else "—/— (not generated)"
        )
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
    ap.add_argument(
        "--outdir",
        type=Path,
        default=Path("/tmp/candidate_b_step0"),
        help="Local/temp output directory (never a tracked results/ path).",
    )
    ap.add_argument(
        "--cases",
        type=str,
        default=",".join(f"{n}:{m}" for n, m in DEFAULT_CASES),
        help="Comma-separated n:m cases. Default includes the (2,4) base-case control.",
    )
    ap.add_argument("--solver", type=str, default="cadical", help="SAT solver executable.")
    ap.add_argument(
        "--max-solve-clauses",
        type=int,
        default=200_000,
        help="Skip solving CNFs larger than this many clauses (keeps Step 0 light).",
    )
    ap.add_argument("--solve-timeout-sec", type=float, default=120.0, help="Per-solve timeout.")
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
        "experiment": "m2.1_step0_equiv_cm_persistence",
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
        "classification_legend": {
            CLASS_EQUIV_CM: "status agrees AND a verified renaming bijection ρ makes the clause multisets coincide",
            CLASS_SAT_EQUIV: "status agrees but no verified ρ (≡CM fails or cannot be established)",
            CLASS_STATUS_DIVERGES: "bundled/split SAT/UNSAT status differs",
            CLASS_INCONCLUSIVE: "generation, parsing, mapping, status, or comparison could not be completed",
        },
        "cases": case_reports,
    }

    report_path = outdir / "step0_comparison.json"
    report_path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    summary_path = outdir / "step0_summary.md"
    summary_path.write_text(_summary_md(payload), encoding="utf-8")

    print(f"Wrote {report_path}")
    print(f"Wrote {summary_path}")
    for r in case_reports:
        c = r["case"]
        print(f"  ({c['n']},{c['m']}): {r['classification']}")
    print("Step 0 only — repair enumeration is NOT authorized until Step 0 is reviewed.")


if __name__ == "__main__":
    main()
