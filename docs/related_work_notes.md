# Related Work Positioning Notes (Phase3 Week2)

## Positioning (short)

This project is positioned as a **verification-first possibility atlas** for small-scope social-choice design: we map axiom lever subsets to SAT/UNSAT outcomes, explain UNSAT frontiers with MUS/MCS, and attach proof-carrying UNSAT evidence (LRAT) checked by Lean. The primary contribution is not a new optimizer; it is an auditable pipeline connecting semantic axiom specs, CNF artifacts, explanation outputs, and kernel-level proof checking.

## Comparison matrix

| Method family | Primary objective | Output artifact | Explanation mode | Optimization vs mapping | Trust model | Typical use |
|---|---|---|---|---|---|---|
| Constraint Hierarchies (CH) | Resolve conflicting constraints with priorities | Feasible assignment under hierarchy | Priority/violation reasoning | Optimization/relaxation-centric | Trust solver/runtime implementation | Constraint satisfaction with soft priorities |
| ATMS | Maintain consistency under assumptions | Justification/dependency structures | Assumption-based derivations | Assumption management-centric | Trust inference engine bookkeeping | Non-monotonic reasoning and diagnosis |
| MAXSAT | Optimize number/weight of satisfied clauses | Optimal/near-optimal model | Unsat cores or cost trade-offs | Optimization-centric | Trust SAT+optimization stack | Soft-constraint optimization |
| OMT | Optimize objective over SMT constraints | Model + objective optimum | Objective/value decomposition | Optimization-centric | Trust SMT+optimization stack | Numeric/logical optimization |
| This repository | Map SAT/UNSAT frontier over axiom lever sets + proof-carrying UNSAT | `atlas.json`, `mus.json`, `mcs.json`, `rule.md`, CNF+LRAT, Lean-checked theorem targets | MUS/MCS frontier explanation + per-case rule sketches | Mapping/explanation/verification-centric (not speed race) | Trust minimized via LRAT + Lean kernel checks for UNSAT claims | Auditable design-space exploration in small scope |

## What we do not claim

- We do **not** claim general `n,m` scalability in this phase.
- We do **not** claim to outperform MAXSAT/OMT on optimization throughput.
- We do **not** claim complete symmetry proof mechanization inside Lean for pruning/reduction heuristics.

## Why this still has value

- Small-scope frontier identification is scientifically useful when impossibility kernels are local and structurally interpretable.
- MUS/MCS provides actionable “which lever blocks feasibility / which minimal repair restores SAT” explanations.
- The pipeline ties semantic intent (`axioms`) to concrete CNF categories (`manifest.category_counts`) and then to verifiable proof artifacts.

## Verification-first value proposition

The differentiator is not raw solve speed; it is the ability to separate:

- **Solve**: external SAT solver exploration,
- **Check**: proof-carrying UNSAT validation (LRAT) by Lean kernel.

This reduces trust in solver internals for final UNSAT claims and provides a stable audit trail for reproducibility discussions.

## Semantics-aware encoding as a differentiator

The repository keeps a transparent bridge:

1. Axiom modules (`encoding/axioms/*.py`) with explicit categories,
2. CNF emission with manifest metadata (`nvars`, `nclauses`, category counts, hashes),
3. Dedicated auditor (`scripts/check_sen24_cnf.py`) for the sen24 baseline/family.

This semantics-aware chain is a key distinction from “opaque optimization run only” workflows.

## When not to use this framing

- If the primary objective is high-dimensional objective optimization (not frontier mapping), MAXSAT/OMT-first may be a better fit.
- If the domain lacks a stable, auditable mapping from assumptions to CNF categories, atlas-style interpretability weakens.
