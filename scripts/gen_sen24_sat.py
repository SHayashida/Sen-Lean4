#!/usr/bin/env python3
"""
Generate a quantifier-free Lean (Std.Tactic.BVDecide) encoding of the Sen base case
(n=2 voters, m=4 alternatives) UNSAT instance:

  UN ∧ MINLIB ∧ SocialAcyclic  is UNSAT

Encoding (SAT, not QBF):
- Variables are ONLY the social strict-preference bits P[p,a,b] for each profile p
  and each ordered pair (a,b) with a≠b.
- Preferences are precomputed in Python and embedded as Bool literals in the Lean formula.

Output:
  SocialChoiceAtlas/Sen/BaseCase24/SATSenGenerated.lean
"""

from __future__ import annotations

import argparse
import itertools
import os
from dataclasses import dataclass
from typing import IO, List, Tuple


NALTS = 4
NVOTERS = 2

RANKINGS: List[Tuple[int, ...]] = list(itertools.permutations(range(NALTS)))
assert len(RANKINGS) == 24

# Fixed ordered-pair order (12 pairs with a≠b)
PAIRS: List[Tuple[int, int]] = [(a, b) for a in range(NALTS) for b in range(NALTS) if a != b]
assert len(PAIRS) == 12


def all_profiles() -> List[Tuple[Tuple[int, ...], Tuple[int, ...]]]:
  # 24^2 = 576 profiles, ordered lexicographically by (r0, r1)
  profiles: List[Tuple[Tuple[int, ...], Tuple[int, ...]]] = []
  for r0 in RANKINGS:
    for r1 in RANKINGS:
      profiles.append((r0, r1))
  return profiles


def positions(r: Tuple[int, ...]) -> List[int]:
  pos = [0] * NALTS
  for i, a in enumerate(r):
    pos[a] = i
  return pos


@dataclass(frozen=True)
class PrefTables:
  pref0: List[List[bool]]  # [p][pairIdx]
  pref1: List[List[bool]]  # [p][pairIdx]
  both: List[List[bool]]   # [p][pairIdx]


def compute_pref_tables(profiles: List[Tuple[Tuple[int, ...], Tuple[int, ...]]]) -> PrefTables:
  pref0: List[List[bool]] = []
  pref1: List[List[bool]] = []
  both: List[List[bool]] = []
  for (r0, r1) in profiles:
    pos0 = positions(r0)
    pos1 = positions(r1)
    row0: List[bool] = []
    row1: List[bool] = []
    rowb: List[bool] = []
    for (a, b) in PAIRS:
      v0 = pos0[a] < pos0[b]
      v1 = pos1[a] < pos1[b]
      row0.append(v0)
      row1.append(v1)
      rowb.append(v0 and v1)
    pref0.append(row0)
    pref1.append(row1)
    both.append(rowb)
  return PrefTables(pref0=pref0, pref1=pref1, both=both)


def emit_balanced_binop(out: IO[str], terms: List[str], op: str, indent: int = 2) -> None:
  """
  Emit a balanced binary tree combining `terms` with `op` (either "&&" or "||").
  This keeps Lean term depth small.
  """

  def go(lo: int, hi: int, cur_indent: int) -> None:
    if hi - lo <= 0:
      out.write("true" if op == "&&" else "false")
      return
    if hi - lo == 1:
      out.write(terms[lo])
      return
    mid = (lo + hi) // 2
    out.write("(")
    go(lo, mid, cur_indent + 1)
    out.write(f"\n{' ' * (cur_indent * indent)}{op} ")
    go(mid, hi, cur_indent + 1)
    out.write(")")

  go(0, len(terms), 1)


def emit_header(out: IO[str], nprofiles: int, nvars: int) -> None:
  out.write("/-\n")
  out.write("THIS FILE IS AUTO-GENERATED.\n\n")
  out.write("Source: scripts/gen_sen24_sat.py\n")
  out.write("Target: SocialChoiceAtlas/Sen/BaseCase24/SATSenGenerated.lean\n\n")
  out.write("Do not edit by hand. Re-run the generator instead.\n")
  out.write("-/\n")
  out.write("import Std.Tactic.BVDecide\n\n")
  out.write("set_option maxRecDepth 10000\n\n")
  out.write("namespace SocialChoiceAtlas.Sen.BaseCase24.SATSenGenerated\n\n")
  out.write(f"abbrev NPROFILES : Nat := {nprofiles}\n")
  out.write("abbrev NPAIRS : Nat := 12\n")
  out.write(f"abbrev NVARS : Nat := {nvars}\n\n")
  out.write("abbrev Assignment := BitVec NVARS\n\n")


def emit_pairIdx(out: IO[str]) -> None:
  out.write("abbrev pairIdx (a b : Nat) : Nat :=\n")
  out.write("  match a, b with\n")
  for idx, (a, b) in enumerate(PAIRS):
    out.write(f"  | {a}, {b} => {idx}\n")
  out.write("  | _, _ => 0\n\n")


def emit_core_defs(out: IO[str]) -> None:
  emit_pairIdx(out)
  out.write("abbrev varIdx (p a b : Nat) : Nat := p * NPAIRS + pairIdx a b\n\n")
  out.write("abbrev P (σ : Assignment) (p a b : Nat) : Bool :=\n")
  out.write("  σ.getLsbD (varIdx p a b)\n\n")


def emit_ASYMM(out: IO[str], nprofiles: int) -> None:
  out.write("abbrev ASYMM (σ : Assignment) : Bool :=\n  ")
  terms: List[str] = []
  for p in range(nprofiles):
    for (a, b) in PAIRS:
      terms.append(f"((!(P σ {p} {a} {b})) || (!(P σ {p} {b} {a})))")
  emit_balanced_binop(out, terms, "&&")
  out.write("\n\n")


def emit_UN(out: IO[str], nprofiles: int, tables: PrefTables) -> None:
  out.write("abbrev UN (σ : Assignment) : Bool :=\n  ")
  terms: List[str] = []
  for p in range(nprofiles):
    for pair_i, (a, b) in enumerate(PAIRS):
      both = tables.both[p][pair_i]
      terms.append(f"((!{str(both).lower()}) || (P σ {p} {a} {b}))")
  emit_balanced_binop(out, terms, "&&")
  out.write("\n\n")


def emit_Dec(out: IO[str], nprofiles: int, tables: PrefTables, voter: int, x: int, y: int) -> None:
  assert voter in (0, 1)
  name = f"Dec{voter}_{x}_{y}"
  out.write(f"abbrev {name} (σ : Assignment) : Bool :=\n  ")
  terms: List[str] = []
  idx_xy = PAIRS.index((x, y))
  for p in range(nprofiles):
    pref = tables.pref0[p][idx_xy] if voter == 0 else tables.pref1[p][idx_xy]
    # Spec form: if pref then Pxy else Pyx. We pre-resolve pref (Bool literal).
    lit = f"(P σ {p} {x} {y})" if pref else f"(P σ {p} {y} {x})"
    terms.append(lit)
  emit_balanced_binop(out, terms, "&&")
  out.write("\n\n")


def emit_MINLIB(out: IO[str]) -> None:
  out.write("abbrev MINLIB (σ : Assignment) : Bool :=\n  ")
  dec0_terms = [f"Dec0_{a}_{b} σ" for (a, b) in PAIRS]
  dec1_terms = [f"Dec1_{a}_{b} σ" for (a, b) in PAIRS]
  out.write("(")
  emit_balanced_binop(out, dec0_terms, "||")
  out.write(")\n  && (")
  emit_balanced_binop(out, dec1_terms, "||")
  out.write(")\n\n")


def emit_NO_CYCLE3(out: IO[str], nprofiles: int) -> None:
  out.write("abbrev NO_CYCLE3 (σ : Assignment) : Bool :=\n  ")
  terms: List[str] = []
  for p in range(nprofiles):
    for a in range(NALTS):
      for b in range(NALTS):
        if b == a:
          continue
        for c in range(NALTS):
          if c == a or c == b:
            continue
          terms.append(
            f"((!(P σ {p} {a} {b})) || (!(P σ {p} {b} {c})) || (!(P σ {p} {c} {a})))"
          )
  emit_balanced_binop(out, terms, "&&")
  out.write("\n\n")


def emit_NO_CYCLE4(out: IO[str], nprofiles: int) -> None:
  out.write("abbrev NO_CYCLE4 (σ : Assignment) : Bool :=\n  ")
  terms: List[str] = []
  for p in range(nprofiles):
    for a in range(NALTS):
      for b in range(NALTS):
        if b == a:
          continue
        for c in range(NALTS):
          if c == a or c == b:
            continue
          for d in range(NALTS):
            if d == a or d == b or d == c:
              continue
            terms.append(
              f"((!(P σ {p} {a} {b})) || (!(P σ {p} {b} {c})) || (!(P σ {p} {c} {d})) || (!(P σ {p} {d} {a})))"
            )
  emit_balanced_binop(out, terms, "&&")
  out.write("\n\n")


def emit_ACYCLIC(out: IO[str]) -> None:
  out.write("abbrev ACYCLIC (σ : Assignment) : Bool :=\n")
  out.write("  NO_CYCLE3 σ && NO_CYCLE4 σ\n\n")


def emit_CONSTRAINTS(out: IO[str]) -> None:
  out.write("abbrev CONSTRAINTS (σ : Assignment) : Bool :=\n")
  out.write("  ASYMM σ && UN σ && MINLIB σ && ACYCLIC σ\n\n")


def emit_theorem(out: IO[str]) -> None:
  out.write("theorem sen24_unsat : ∀ σ : Assignment, CONSTRAINTS σ = false := by\n")
  out.write("  bv_decide\n\n")
  out.write("/-\n")
  out.write("LRAT caching:\n\n")
  out.write("- Change the proof to `bv_decide?`.\n")
  out.write("- Run Lean on this file via an *absolute path* so it can write the `.lrat` next to it:\n")
  out.write("    lake env lean /ABS/PATH/TO/SocialChoiceAtlas/Sen/BaseCase24/SATSenGenerated.lean\n")
  out.write("- Commit the generated `.lrat` and switch the proof to:\n")
  out.write("    by bv_check \"sen24_unsat.lrat\"\n")
  out.write("-/\n\n")
  out.write("end SocialChoiceAtlas.Sen.BaseCase24.SATSenGenerated\n")


def main() -> None:
  parser = argparse.ArgumentParser()
  parser.add_argument(
    "--profiles",
    choices=["all"],
    default="all",
    help="Currently only 'all' profiles (24^2=576) is supported.",
  )
  parser.add_argument(
    "--out",
    default=None,
    help="Output path (defaults to SocialChoiceAtlas/Sen/BaseCase24/SATSenGenerated.lean).",
  )
  args = parser.parse_args()

  profiles = all_profiles()
  nprofiles = len(profiles)
  nvars = nprofiles * len(PAIRS)
  tables = compute_pref_tables(profiles)

  out_path = args.out
  if out_path is None:
    out_path = os.path.normpath(
      os.path.join(
        os.path.dirname(__file__),
        "..",
        "SocialChoiceAtlas",
        "Sen",
        "BaseCase24",
        "SATSenGenerated.lean",
      )
    )

  os.makedirs(os.path.dirname(out_path), exist_ok=True)
  with open(out_path, "w", encoding="utf-8") as out:
    emit_header(out, nprofiles=nprofiles, nvars=nvars)
    emit_core_defs(out)
    emit_ASYMM(out, nprofiles=nprofiles)
    emit_UN(out, nprofiles=nprofiles, tables=tables)
    for (a, b) in PAIRS:
      emit_Dec(out, nprofiles=nprofiles, tables=tables, voter=0, x=a, y=b)
    for (a, b) in PAIRS:
      emit_Dec(out, nprofiles=nprofiles, tables=tables, voter=1, x=a, y=b)
    emit_MINLIB(out)
    emit_NO_CYCLE3(out, nprofiles=nprofiles)
    emit_NO_CYCLE4(out, nprofiles=nprofiles)
    emit_ACYCLIC(out)
    emit_CONSTRAINTS(out)
    emit_theorem(out)

  print(f"Wrote: {out_path}")


if __name__ == "__main__":
  main()

