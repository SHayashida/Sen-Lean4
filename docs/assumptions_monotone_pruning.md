# Assumptions: Monotone Pruning Safety (sen24)

## Scope

This note specifies when `scripts/run_atlas.py --prune monotone` is sound for the fixed sen24 setup (`n=2`, `m=4`).

## Order-theoretic setup

- Let `U` be the axiom universe (`axiom_universe` in `atlas.json`).
- A case is an axiom set `S ⊆ U`, encoded by a stable bitmask `case_<bitstring>`.
- "Stronger" means **more axioms enabled** (set inclusion).

## Monotone facts used by pruning

For conjunction-only encodings:

- If `CNF(S)` is SAT, then for any `T ⊆ S`, `CNF(T)` is SAT (SAT is downward-closed).
- If `CNF(S)` is UNSAT, then for any `T ⊇ S`, `CNF(T)` is UNSAT (UNSAT is upward-closed).

These are exactly the two rules used for inference in prune mode.

## Required assumptions in this repository

The pruning logic is sound only if all of the following hold:

1. **Conjunctive toggles only**: each axiom switch only adds clauses (no clause removal under the same mask order).
2. **Stable semantics**: toggles do not change the meaning of existing `P` variables.
3. **No semantic rewrite by options**: options only choose conjunction subsets, not alternate semantic encodings.

About auxiliary variables (e.g. MINLIB selectors):

- Aux ranges may appear/disappear by toggle.
- This is still monotone-safe under existential SAT semantics, because adding a new constrained block is conjunction with extra existentially quantified variables.

## Atlas semantics for solved/inferred cases

- `solved=true`: SAT solver actually executed for this case.
- `solved=false`: status inferred by monotone pruning (no solver call for this case).

## Evidence contract for inferred cases

For any inferred SAT/UNSAT case (`solved=false`), `pruned_by` must include:

- `derived_status` (`SAT` or `UNSAT`)
- `rule` (`subset_of_sat` or `superset_of_unsat`)
- `witness_case_id` (must exist in atlas and have `solved=true`)

Additional invariants checked in code:

- witness status equals derived status,
- witness lattice relation matches rule:
  - `subset_of_sat`: `case_mask ⊆ witness_mask`
  - `superset_of_unsat`: `witness_mask ⊆ case_mask`

Validation failure is fatal (`run_atlas.py` aborts).

## `--prune-check`

`--prune-check` performs deterministic spot checks:

- sample a fixed small set of inferred cases,
- re-solve directly,
- compare observed SAT/UNSAT with inferred status.

Any mismatch aborts the run.

## When NOT to use monotone pruning

Do not use prune mode when toggles are non-monotone, for example:

- toggles that rewrite semantics instead of adding conjunction constraints,
- labeled/role-based mode switches that alter interpretation of existing variables,
- parameterized weakenings not representable as pure ON/OFF conjunctive additions.
