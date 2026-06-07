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

A family-scale split encoding of the liberalism layer is required before ≡CM
persistence can be measured beyond `(2,4)`. **Option D (below) supplies this for
the `(2,m)` positive track using a legacy-style two-series split — deliberately
NOT `pair_selectors_v1`.** The voter-dimension (`n > 2`, e.g. `(3,4)`) remains the
Option C boundary track and is not implemented here.

---

## Option D — legacy-style `(2,m)` two-witness split (positive track)

Files:

- `option_d_encoder.py` — isolated encoder; generalizes the legacy Sen24
  `selectors_v1` two-series MINLIB layout from `(2,4)` to `(2,m)`, with `n = 2`
  fixed. Does **not** modify `encoding/schema.py`.
- `step0_equiv_check_option_d.py` — Step 0 rerun that uses the Option D encoder
  and reuses the base checker's ρ-construction and classification logic.

Run:

    python3 scripts/exploration/candidate_b/step0_equiv_check_option_d.py

Default cases: `2:4` (control), `2:5` (Option D positive-track case). Outputs go
to `/tmp/candidate_b_step0_option_d/`.

### Option D vs Option C — the precise distinction

- **Option D (this encoder) = legacy-style two-voter split, NO pair selector.**
  The liberalism layer is exposed through two direct selector series analogous to
  legacy `sel0` / `sel1`:
  - `sel0(a,b)` ↦ voter-0 decisiveness (lever `decisive_voter0`),
  - `sel1(a,b)` ↦ voter-1 decisiveness (lever `decisive_voter1`).

  Bundled `minlib` emits both series; split emits `decisive_voter0` (sel0) and
  `decisive_voter1` (sel1). The bundled `minlib` clause multiset equals the union
  of the two split series over identical variables, so an **identity** ρ
  witnesses ≡CM. There are **no** voter-pair selector variables and **no**
  pair-selection clauses.
- **Option C / parametric `pair_selectors_v1` = voter-pair selector machinery**
  (`var_minlib_pair(i,j)` plus pair-selection clauses). That extra machinery is
  what risks breaking ≡CM, so it is **not reused** for Option D. Even at `(2,5)`,
  where `C(2,2)=1`, `pair_selectors_v1` would introduce selector clauses absent
  from the legacy M1.5 split structure, which is precisely why Option D uses the
  legacy-style series instead.

### Option D Step 0 outcome

| case | classification | note |
| --- | --- | --- |
| (2,4) | `equiv_cm_persists` | control; identity ρ verified, UNSAT/UNSAT; clause multiset byte-identical to the real generator |
| (2,5) | `equiv_cm_persists` | positive track; identity ρ verified, UNSAT/UNSAT; `uses_pair_selectors=false` |

The `(2,5)` result is for the `(2,m)` positive track **only**; it does **not**
settle the Option C / voter-dimension boundary track (`n > 2`, e.g. `(3,4)`).
Repair enumeration remains unauthorized.
