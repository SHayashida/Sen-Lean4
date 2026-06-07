# M2.1 Candidate-B exploration (Step 0)

Exploratory, **isolated** prototypes for M2.1 Step 0. Nothing here is promoted to
top-level `scripts/`. Outputs are written to a temp/local path
(default `/tmp/candidate_b_step0`), never into tracked `results/`.

Step 0 only. **Repair enumeration is not authorized until Step 0 is reviewed.**

## What Step 0 asks

Does the M1.5 bundled/split **clause-multiset equivalence (≡CM)** persist at
larger finite cases under the repair-transport map π?

    π(minlib)    = {decisive_voter0, decisive_voter1}
    π(asymm)     = {asymm}
    π(un)        = {un}
    π(no_cycle3) = {no_cycle3}
    π(no_cycle4) = {no_cycle4}

π is a lever correspondence / repair-transport map, not a semantic equivalence
claim between axiom formulas.

## Checker

`step0_equiv_check.py` reuses the existing generator (`scripts/gen_dimacs.py`,
`run_generation`) to produce the bundled package and its π-image (split) package
per case, then attempts to **construct and verify** a variable-renaming bijection
ρ under which the two clause multisets coincide (M1.5 Definition-2 sense).

`equiv_cm_persists` is asserted only when ρ is actually built and re-verified.
Equal variable/clause counts are necessary but never sufficient.

Run:

    python3 scripts/exploration/candidate_b/step0_equiv_check.py

Default cases: `2:4` (M1.5 base-case control), `2:5`, `3:4`.

## Current Step 0 outcome

| case | classification | note |
| --- | --- | --- |
| (2,4) | `equiv_cm_persists` | base-case control; identity ρ verified, UNSAT/UNSAT |
| (2,5) | `inconclusive` | split package not generable (see below) |
| (3,4) | `inconclusive` | split package not generable (see below) |

## Missing generator interface (the Step 0 blocker)

The split levers `decisive_voter0` / `decisive_voter1`
(`encoding/axioms/decisive_voter0.py`, `decisive_voter1.py`) require the legacy
`selectors_v1` MINLIB mode, which `encoding/schema.py` restricts to the Sen24
base case `(2,4)`:

- `FiniteSchema.__init__` rejects `selectors_v1` for `(n,m) != (2,4)`;
- `resolve_minlib_mode("auto", …)` returns the parametric `pair_selectors_v1`
  mode for cases beyond `(2,4)`, in which the split levers are not defined;
- `decisive_voter0.encode` / `decisive_voter1.encode` raise unless the schema is
  in `selectors_v1` mode.

So at `(2,5)` and `(3,4)` the bundled package generates (parametric mode) but the
π-image split package cannot be generated at all. ≡CM is therefore not evaluable
and the cases are `inconclusive` by generation, not by a checker fault.

Additional structural caveat: the transport map fixes a **two-lever** split image
`{decisive_voter0, decisive_voter1}`. At cases with more than two voters
(e.g. `n = 3` in `(3,4)`) a two-element split image may be structurally
insufficient to account for all `minlib` clauses even once a parametric split
encoding exists, so ρ may legitimately fail to exist there. That is a finding
about the transport map's scope, to be recorded — not force-fitted.

### What a future Step 0 needs

A family-scale split encoding of the liberalism layer — i.e. a parametric
analogue of `decisive_voter*` that is defined under `pair_selectors_v1` for
`(2,5)` and `(3,4)`, with an explicit per-voter decisive-lever scheme — before
≡CM persistence can be measured. Designing that encoding is itself part of the
Step 0 review and is out of scope for this exploratory checker.
