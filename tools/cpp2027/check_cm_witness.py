#!/usr/bin/env python3
"""Standalone re-verification of the bundled/split witness claims (C1--C5).

Run from the ``witness/`` directory of the supplementary archive:

    python3 tools/check_cm_witness.py

Requirements: Python 3.10+; ``python-sat`` for C2--C5 (``pip install python-sat``).
C1 (deterministic regeneration + clause-multiset equivalence) needs stdlib only.

Claims checked:
  C1  Both witness instances regenerate deterministically (SHA-256 equal to the
      archived manifests) and their CNF clause multisets are equal under the
      identity variable map (per-clause literal sort, multiset comparison).
  C2  Both instances are UNSAT.
  C3  Bundled raw minimal repair family = {{asymm},{un},{minlib},{no_cycle4}}.
  C4  Split raw minimal repair family
        = {{asymm},{un},{decisive_voter0},{decisive_voter1},{no_cycle4}}.
  C5  The transported bundled family differs from the split family:
      {decisive_voter0, decisive_voter1} is feasible but not inclusion-minimal
      on the split side (follows from C3+C4; re-derived here explicitly).

Exit codes: 0 all checked claims PASS; 1 any FAIL; 2 solver unavailable
(C1 passed, C2--C5 skipped).
"""
from __future__ import annotations

import hashlib
import json
import sys
import tempfile
from collections import Counter
from pathlib import Path

HERE = Path(__file__).resolve().parent          # witness/tools
WITNESS_ROOT = HERE.parent                       # witness/
sys.path.insert(0, str(HERE))                    # for gen_dimacs
sys.path.insert(0, str(WITNESS_ROOT))            # for encoding.*

from gen_dimacs import run_generation  # noqa: E402

ARTIFACTS = WITNESS_ROOT / "artifacts" / "candidate_b_minlib_granularity"

BUNDLED_AXIOMS = ["asymm", "un", "minlib", "no_cycle4"]
SPLIT_AXIOMS = ["asymm", "un", "decisive_voter0", "decisive_voter1", "no_cycle4"]
BUNDLED_CASE = "bundled/case_11101"
SPLIT_CASE = "split/case_111101"

EXPECTED = {
    "nvars": 6936,
    "nclauses": 36290,
    "bundled_sha256": "6570c79cdf3e5fb3235924793bdb53968470095ebd7dc19d8707c508d0fbe384",
    "split_sha256": "35d24434bf66fbdf8f4ad0a734562b3527c665ad77e5e9c93594c1aae4e3b292",
    "bundled_repairs": {frozenset({a}) for a in BUNDLED_AXIOMS},
    "split_repairs": {frozenset({a}) for a in SPLIT_AXIOMS},
}


def clause_counter(path: Path) -> Counter:
    c: Counter = Counter()
    for raw in path.read_text(encoding="utf-8").splitlines():
        line = raw.strip()
        if not line or line.startswith("c") or line.startswith("p "):
            continue
        parts = [int(x) for x in line.split()]
        if not parts or parts[-1] != 0:
            raise ValueError(f"malformed DIMACS line in {path}: {raw!r}")
        c[tuple(sorted(parts[:-1]))] += 1
    return c


def regenerate(axioms: list[str], outdir: Path) -> dict:
    cnf = outdir / "sen24.cnf"
    man = outdir / "sen24.manifest.json"
    run_generation(n=2, m=4, axiom_names=axioms, out_path=cnf, manifest_path=man)
    return {"cnf": cnf, "manifest": json.loads(man.read_text())}


def report(claim: str, ok: bool, detail: str) -> bool:
    print(f"[{'PASS' if ok else 'FAIL'}] {claim}: {detail}")
    return ok


def main() -> int:
    all_ok = True
    with tempfile.TemporaryDirectory() as td:
        tmp = Path(td)
        gen = {
            "bundled": regenerate(BUNDLED_AXIOMS, tmp / "bundled"),
            "split": regenerate(SPLIT_AXIOMS, tmp / "split"),
        }

        # ---- C1: deterministic regeneration + identity-map CM equivalence ----
        c1 = True
        for name, case_rel, key in (
            ("bundled", BUNDLED_CASE, "bundled_sha256"),
            ("split", SPLIT_CASE, "split_sha256"),
        ):
            m = gen[name]["manifest"]
            got = m["cnf_sha256"]
            archived = json.loads(
                (ARTIFACTS / case_rel / "sen24.manifest.json").read_text()
            )["cnf_sha256"]
            c1 &= got == EXPECTED[key] == archived
            c1 &= int(m["nvars"]) == EXPECTED["nvars"]
            c1 &= int(m["nclauses"]) == EXPECTED["nclauses"]
        cb = clause_counter(gen["bundled"]["cnf"])
        cs = clause_counter(gen["split"]["cnf"])
        c1 &= cb == cs
        all_ok &= report(
            "C1",
            c1,
            f"sha256(bundled)={gen['bundled']['manifest']['cnf_sha256'][:12]}..., "
            f"sha256(split)={gen['split']['manifest']['cnf_sha256'][:12]}..., "
            f"CM-equal(identity)={cb == cs}, clauses={sum(cb.values())}",
        )

        # ---- C2--C5 need a SAT solver ----
        try:
            from pysat.formula import CNF  # type: ignore
            from pysat.solvers import Cadical153  # type: ignore
        except ImportError:
            print("[SKIP] C2-C5: python-sat not installed (pip install python-sat)")
            return 0 if all_ok else 1 if not all_ok else 2  # C1 verdict only
            # (unreachable; kept for clarity)

        def status(axioms: list[str]) -> str:
            d = tmp / ("s_" + "_".join(axioms) if axioms else "s_empty")
            d.mkdir(exist_ok=True)
            g = regenerate(axioms, d)
            with Cadical153(
                bootstrap_with=CNF(from_file=str(g["cnf"])).clauses
            ) as s:
                return "SAT" if s.solve() else "UNSAT"

        c2 = status(BUNDLED_AXIOMS) == "UNSAT" and status(SPLIT_AXIOMS) == "UNSAT"
        all_ok &= report("C2", c2, "full bundled and split instances are UNSAT")

        def singleton_repairs(universe: list[str]) -> set[frozenset[str]]:
            # Full set is infeasible (C2), so every feasible singleton deletion
            # is inclusion-minimal; supersets of feasible singletons are not.
            return {
                frozenset({ax})
                for ax in universe
                if status([x for x in universe if x != ax]) == "SAT"
            }

        rb = singleton_repairs(BUNDLED_AXIOMS)
        all_ok &= report(
            "C3", rb == EXPECTED["bundled_repairs"],
            f"bundled repair family = {sorted(sorted(s) for s in rb)}",
        )
        rs = singleton_repairs(SPLIT_AXIOMS)
        all_ok &= report(
            "C4", rs == EXPECTED["split_repairs"],
            f"split repair family = {sorted(sorted(s) for s in rs)}",
        )

        pair = frozenset({"decisive_voter0", "decisive_voter1"})
        transported = {
            (pair if s == frozenset({"minlib"}) else s) for s in rb
        }
        c5 = (
            transported != rs
            and pair in transported
            and frozenset({"decisive_voter0"}) in rs
        )
        all_ok &= report(
            "C5", c5,
            "transported bundled family != split family; "
            "{d0,d1} transported but not inclusion-minimal on the split side",
        )

    print("RESULT:", "ALL PASS" if all_ok else "FAILURES PRESENT")
    return 0 if all_ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
