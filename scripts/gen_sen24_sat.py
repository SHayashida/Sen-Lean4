#!/usr/bin/env python3
"""
Generate a quantifier-free Lean (Std.Tactic.BVDecide) encoding of the Sen base case
(n=2 voters, m=4 alternatives) UNSAT instance:

  UN ∧ MINLIB ∧ SocialAcyclic  is UNSAT

We encode only the social strict preference bits P[p,a,b] (a≠b), for all 576
profiles p (pairs of rankings), and enforce:
- Asymmetry
- UN (using precomputed bothPrefer constants)
- MINLIB (existence of decisive ordered pairs for voter0 and voter1)
- Acyclicity via forbidding all 3-cycles and 4-cycles (sufficient on 4 alts;
  2-cycles are excluded by asymmetry)

The generated Lean file contains only Bool/BitVec/if/&&/||/not/bit extraction.
No List/perm computations occur in the SAT goal; all preference facts are baked
in as Bool literals.
"""

from __future__ import annotations

import itertools
import os
from dataclasses import dataclass
from typing import IO, Iterable, List, Tuple


NALTS = 4
NVOTERS = 2
RANKINGS: List[Tuple[int, ...]] = list(itertools.permutations(range(NALTS)))
assert len(RANKINGS) == 24

PAIRS: List[Tuple[int, int]] = [(a, b) for a in range(NALTS) for b in range(NALTS) if a != b]
assert len(PAIRS) == 12

NPROFILES = len(RANKINGS) ** NVOTERS  # 24^2 = 576
NPAIRS = len(PAIRS)  # 12
NVARS = NPROFILES * NPAIRS  # 6912


def profile_of_index(p: int) -> Tuple[Tuple[int, ...], Tuple[int, ...]]:
  r0_idx = p // len(RANKINGS)
  r1_idx = p % len(RANKINGS)
  return (RANKINGS[r0_idx], RANKINGS[r1_idx])


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


def compute_pref_tables() -> PrefTables:
  pref0: List[List[bool]] = []
  pref1: List[List[bool]] = []
  both: List[List[bool]] = []

  for p in range(NPROFILES):
    r0, r1 = profile_of_index(p)
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


def lean_bool(b: bool) -> str:
  return "true" if b else "false"


def emit_balanced_binop(
  out: IO[str],
  terms: List[str],
  op: str,
  indent: int = 2,
) -> None:
  """
  Emit a balanced binary tree combining `terms` with `op` (either "&&" or "||").
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


def emit_pairIdx(out: IO[str]) -> None:
  out.write("abbrev pairIdx (a b : Nat) : Nat :=\n")
  out.write("  match a, b with\n")
  idx = 0
  for (a, b) in PAIRS:
    out.write(f"  | {a}, {b} => {idx}\n")
    idx += 1
  out.write("  | _, _ => 0\n\n")


def emit_header(out: IO[str]) -> None:
  out.write("/-\n")
  out.write("THIS FILE IS AUTO-GENERATED.\n\n")
  out.write("Source: scripts/gen_sen24_sat.py\n")
  out.write("Target: SocialChoiceAtlas/Sen/BaseCase24/SATSenGenerated.lean\n\n")
  out.write("Do not edit by hand. Re-run the generator instead.\n")
  out.write("-/\n")
  out.write("import Std.Tactic.BVDecide\n\n")
  out.write("set_option maxRecDepth 10000\n\n")
  out.write("namespace SocialChoiceAtlas.Sen.BaseCase24.SATSenGenerated\n\n")
  out.write(f"abbrev NPROFILES : Nat := {NPROFILES}\n")
  out.write(f"abbrev NPAIRS : Nat := {NPAIRS}\n")
  out.write(f"abbrev NVARS : Nat := {NVARS}\n\n")
  out.write("abbrev Assignment := BitVec NVARS\n\n")


def emit_core_defs(out: IO[str]) -> None:
  emit_pairIdx(out)
  out.write("abbrev varIdx (p a b : Nat) : Nat := p * NPAIRS + pairIdx a b\n\n")
  out.write("abbrev P (σ : Assignment) (p a b : Nat) : Bool :=\n")
  out.write("  σ.getLsbD (varIdx p a b)\n\n")


def emit_ASYMM(out: IO[str]) -> None:
  out.write("abbrev ASYMM (σ : Assignment) : Bool :=\n  ")
  terms: List[str] = []
  for p in range(NPROFILES):
    for (a, b) in PAIRS:
      terms.append(f"((!(P σ {p} {a} {b})) || (!(P σ {p} {b} {a})))")
  emit_balanced_binop(out, terms, "&&")
  out.write("\n\n")


def emit_UN(out: IO[str], tables: PrefTables) -> None:
  out.write("abbrev UN (σ : Assignment) : Bool :=\n  ")
  terms: List[str] = []
  for p in range(NPROFILES):
    for pair_i, (a, b) in enumerate(PAIRS):
      both = tables.both[p][pair_i]
      # (!bothPrefer) || P
      terms.append(f"((!{lean_bool(both)}) || (P σ {p} {a} {b}))")
  emit_balanced_binop(out, terms, "&&")
  out.write("\n\n")


def emit_Dec(out: IO[str], tables: PrefTables, voter: int, x: int, y: int) -> None:
  assert voter in (0, 1)
  name = f"Dec{voter}_{x}_{y}"
  out.write(f"abbrev {name} (σ : Assignment) : Bool :=\n  ")
  terms: List[str] = []
  # pair index for (x,y) and (y,x)
  p_xy = PAIRS.index((x, y))
  for p in range(NPROFILES):
    pref = tables.pref0[p][p_xy] if voter == 0 else tables.pref1[p][p_xy]
    terms.append(
      f"(if {lean_bool(pref)} then (P σ {p} {x} {y}) else (P σ {p} {y} {x}))"
    )
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


def emit_NO_CYCLE3(out: IO[str]) -> None:
  out.write("abbrev NO_CYCLE3 (σ : Assignment) : Bool :=\n  ")
  terms: List[str] = []
  for p in range(NPROFILES):
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


def emit_NO_CYCLE4(out: IO[str]) -> None:
  out.write("abbrev NO_CYCLE4 (σ : Assignment) : Bool :=\n  ")
  terms: List[str] = []
  for p in range(NPROFILES):
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
  out.write("Certificate caching workflow (LRAT):\n\n")
  out.write("1) Temporarily change the proof above to `bv_decide?` and build this module:\n")
  out.write("     lake build SocialChoiceAtlas.Sen.BaseCase24.SATSenGenerated\n\n")
  out.write("2) `bv_decide?` will propose a `bv_check` proof plus a `.lrat` file.\n")
  out.write("   Commit the `.lrat` file next to this Lean file.\n\n")
  out.write("3) Replace the proof by:\n")
  out.write("     by\n")
  out.write("       bv_check \"sen24_unsat.lrat\"\n\n")
  out.write("The resulting proof is deterministic and checks the LRAT certificate.\n")
  out.write("-/\n\n")
  out.write("end SocialChoiceAtlas.Sen.BaseCase24.SATSenGenerated\n")


def main() -> None:
  tables = compute_pref_tables()

  out_path = os.path.join(
    os.path.dirname(__file__),
    "..",
    "SocialChoiceAtlas",
    "Sen",
    "BaseCase24",
    "SATSenGenerated.lean",
  )
  out_path = os.path.normpath(out_path)
  os.makedirs(os.path.dirname(out_path), exist_ok=True)

  with open(out_path, "w", encoding="utf-8") as out:
    emit_header(out)
    emit_core_defs(out)
    emit_ASYMM(out)
    emit_UN(out, tables)
    # Decisive constraints for each ordered pair, for each voter.
    for (a, b) in PAIRS:
      emit_Dec(out, tables, voter=0, x=a, y=b)
    for (a, b) in PAIRS:
      emit_Dec(out, tables, voter=1, x=a, y=b)
    emit_MINLIB(out)
    emit_NO_CYCLE3(out)
    emit_NO_CYCLE4(out)
    emit_ACYCLIC(out)
    emit_CONSTRAINTS(out)
    emit_theorem(out)

  print(f"Wrote: {out_path}")


if __name__ == "__main__":
  main()
