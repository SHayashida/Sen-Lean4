# Supplementary Archive — Reproduction Guide

This archive accompanies the anonymous submission
*Certified Impossibility Witnesses Do Not Determine Repair Reports:
A Lean-Verified Characterization of Contract-Relative Reportability*.

It contains two independent components and a machine-checkable manifest.

```
lean/                      Kernel-checked Lean 4 development (characterization
                           theorems; paper Sections 4–5 and 7)
witness/                   SAT witness for the no-go theorem (paper Section 3)
  encoding/                Deterministic CNF generator (Python, stdlib only)
  tools/gen_dimacs.py      Generator entry point
  tools/check_cm_witness.py  One-command re-verification of claims C1–C5
  artifacts/…              Archived experiment tree (manifests, atlases,
                           repair summaries, comparison records)
MANIFEST.sha256            SHA-256 of every file in this archive
```

`candidate_b` in artifact paths and JSON fields is an internal experiment
codename with no external meaning; it is retained verbatim to preserve the
integrity of the archived records.

## 1. Verify archive integrity

```
sha256sum -c MANIFEST.sha256
```

## 2. Re-verify the witness claims (C1–C5)

Requirements: Python ≥ 3.10; `python-sat` for C2–C5.

```
cd witness
pip install python-sat
python3 tools/check_cm_witness.py
```

Expected output: `PASS` for C1–C5 and `RESULT: ALL PASS`.

| Claim | Statement | Paper reference |
|---|---|---|
| C1 | Both witness instances regenerate deterministically (SHA-256 equal to the archived manifests, 6,936 variables / 36,290 clauses each) and are clause-multiset equivalent under the **identity** variable map | §3, Thm. condition (1) |
| C2 | Both instances are UNSAT (re-solved with CaDiCaL via python-sat) | §3, condition (2) |
| C3 | Bundled raw minimal repair family = {{asymm},{un},{minlib},{no_cycle4}} | §3, Step 3 |
| C4 | Split raw minimal repair family = {{asymm},{un},{decisive_voter0},{decisive_voter1},{no_cycle4}} | §3, Step 5 |
| C5 | Transported bundled family ≠ split family; {decisive_voter0, decisive_voter1} is transported but not inclusion-minimal on the split side | §3, condition (3) |

Notes. The generator is deterministic, so the CNFs themselves are not stored;
C1 binds the regenerated files to the archived manifests by SHA-256.
Because the full instances are infeasible (C2), a singleton deletion is
inclusion-minimal iff it restores satisfiability; C3–C4 therefore check all
singleton deletions exhaustively. C5 is a set-level consequence of C1–C4 and
is re-derived explicitly by the checker.

The archived tree `witness/artifacts/…` additionally contains the full
32-case bundled atlas, 64-case split atlas, the case-by-case mapped
comparison (`comparison.json`), and per-case manifests, matching the
appendix tables.

## 3. Build the Lean development

Requirements: `elan` (Lean version manager); network access for the Mathlib
cache on first build.

```
cd lean
lake exe cache get   # fetch Mathlib build cache
lake build
```

The paper-facing theorems are under `SocialChoiceAtlas/Reportability/`:

| Paper | Lean identifier | File |
|---|---|---|
| Thm (coincidence, atomic case) | `m3a_grouped_correctness`, `m3a_raw_transport` | `Atomic.lean` |
| Thm (sufficiency) | `m3b_grouped_correctness` | `GroupSound.lean` |
| Cor (two-realization invariance) | `m3b_two_realization` | `GroupSound.lean` |
| Thm (converse) | `m3c_converse` | `Monotone.lean` |
| Thm (characterization, iff) | `groupSoundness_iff` | `Monotone.lean` |
| Lem (hierarchy) | `atomicity_implies_groupSoundness` | `Monotone.lean` |
| Counterexamples (necessity of hypotheses) | see module | `Examples.lean` |

The development contains no `sorry` or `admit`; this can be confirmed with

```
grep -rn "sorry\|admit" SocialChoiceAtlas/Reportability/
```

The artifact-level soundness audit of the witness pair (paper Section 6) is
deliberately **not** formalized; the Lean development and the SAT witness are
independent evidence layers, as stated in the paper's claim-boundary
discussion.
