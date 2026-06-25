# Candidate B: Option C Voter-Boundary Plan (M2.1)

**Status:** Step 0 feasibility implemented and measured. This note does not
authorize repair enumeration or promotion of the exploratory encoder.

**Result note:** See
[docs/candidate_b_option_c_boundary_result.md](candidate_b_option_c_boundary_result.md)
for the finalized `(3,4)` Step 0 evidence.

## 1. Purpose

This note defines the M2.1 Option C boundary track for `(3,4)`. It was written
before encoder changes and now records the resulting Step 0 feasibility
classification.

The plan exists to determine whether the M1.5 repair-presentation witness class
can be extended from two voters to more than two voters while preserving
clause-multiset equivalence (≡CM).

## 2. Relation to Option D

Option D is the completed positive track. It established that the M1.5
repair-presentation non-canonicity persists from `(2,4)` to `(2,5)` under ≡CM
when the voter count remains fixed at two and the alternative dimension
increases.

Option D must not be re-opened by this plan. Option C asks a different question:
what happens when the voter dimension increases? The pending boundary case is
`(3,4)`, where the split representation must identify two witnesses among more
than two voters.

## 3. Design Question

Option C is the pair-selector split with repair-transport map:

```text
π(minlib)    = {selected_decisive_left, selected_decisive_right}
π(asymm)     = {asymm}
π(un)        = {un}
π(no_cycle3) = {no_cycle3}
π(no_cycle4) = {no_cycle4}
```

The image of `minlib` is intended to represent the two selected decisive
witnesses required by MINLIB when `n > 2`. The map `π` is a lever
correspondence and repair-transport map, not a semantic equivalence claim.

The Step 0 design question is whether a pair-selector realization at `(3,4)`
can produce a split package that remains comparable to the bundled package
under a verified variable-renaming bijection `ρ`.

## 4. Core Risk

Option C may require:

- pair-selector variables that identify the selected voter pair;
- decisive-selector variables that expose the left and right witnesses;
- witness-pair selection clauses and selector-to-decisiveness implications.

These variables and clauses may have no counterparts in the bundled encoding.
If unmatched selector machinery is present only on the split side, the bundled
and split clause multisets may differ under every variable renaming, breaking
≡CM even when SAT/UNSAT status agrees.

This risk is the object of the boundary experiment. It must not be hidden by
assuming that a satisfiability-equivalent pair-selector encoding is also ≡CM.

## 5. Step 0 Boundary Classification

The Option C Step 0 check for `(3,4)` uses exactly one of the existing
classifications:

- `equiv_cm_persists`
- `sat_equiv_only`
- `status_diverges`
- `inconclusive`

The report must record bundled and split generation status, exact SAT/UNSAT
status, variable and clause counts, selector-specific clause categories, and
the result of constructing and verifying `ρ`. Equal counts alone are not
sufficient for `equiv_cm_persists`.

## 6. Interpretation Rules

- If the classification is `equiv_cm_persists`, Option C may support a strong
  voter-dimension extension of the M1.5 witness class. Repair enumeration would
  still require explicit review and separate authorization.
- If the classification is `sat_equiv_only`, the comparison may remain useful,
  but the M1.5-style ≡CM shield is lost. Any later repair divergence must be
  framed as weaker than the Option D positive result because selector or
  encoding-strength differences have not been ruled out.
- If the classification is `status_diverges`, do not claim
  repair-representation non-canonicity. Record an encoding-transfer boundary
  between the bundled and pair-selector representations.
- If the classification is `inconclusive`, do not proceed to repair
  enumeration. Resolve the generation, solver, or equivalence-checking blocker
  before interpreting the case.

None of these rules authorizes repair enumeration through this planning note.

## 7. Boundary-Result Framing

Failure of ≡CM at `(3,4)` is not necessarily a failure of M2.1. It may be a
valid negative boundary result:

> In the tested `(2,5)` case, M1.5's witness class transfers cleanly along the
> two-voter alternative-expansion track; in the tested `(3,4)` case, it does
> not automatically transfer along the voter-dimension track.

This framing would complement, rather than weaken, the completed Option D
positive track. Option D establishes persistence under fixed two-voter witness
structure; Option C tests where additional witness-selection machinery changes
the representation class.

The boundary claim must be based on the reviewed Step 0 evidence. It must not
be inferred merely from the expectation that pair selectors add clauses.

## 8. Constraints on Further Implementation

For any work after the current Step 0 implementation:

- keep every prototype under `scripts/exploration/candidate_b/`;
- do not promote anything to top-level `scripts/`;
- do not modify `encoding/schema.py` unless a later promotion stage explicitly
  authorizes that change;
- do not modify Lean files, M2 theorem statements, M2 paper claims, or baseline
  CNF/LRAT certificates;
- write exploratory outputs only to local temporary paths, not tracked
  `results/`;
- run Step 0 for `(3,4)` before any repair enumeration;
- do not begin repair enumeration until the Step 0 classification and any
  weakening from ≡CM have been explicitly reviewed.

This document does not authorize further Option C encoder changes, a schema
change, promotion, or repair enumeration.

## 9. Scope Caveat

The boundary track remains inside the local-rationality family:
`no_cycle3 ∧ no_cycle4` is not full `SocialAcyclic` at family scale.

The Sen24 CNF witness is not a family-level CNF certificate. Option C planning
does not alter M2, does not change any M2 theorem or paper claim, and does not
extend the scope of the existing baseline certificates.

## 10. Step 0 Feasibility Result

The authorized exploratory implementation lives under
`scripts/exploration/candidate_b/`:

- `option_c_encoder.py`
- `step0_equiv_check_option_c.py`

The bundled side uses the repository's existing `pair_selectors_v1` generator.
The split side uses one shared witness-pair selector bank and separate
left/right decisive-selector banks. This is necessary for the split levers to
represent their roles independently: at `(3,4)`, voter 1 can be the right member
of pair `(0,1)` or the left member of pair `(1,2)`.

The measured result is:

- bundled status: `UNSAT`;
- split status: `UNSAT`;
- classification: `sat_equiv_only`;
- bundled variables/clauses: `165,927 / 1,347,847`;
- split variables/clauses: `165,939 / 1,513,735`;
- structural delta: 12 variables and 165,888 binary implication clauses.

The variable count, clause count, and clause-length histogram all differ.
Because these are invariants under variable renaming, no bijection `ρ` can make
the clause multisets equal. The Option C selector representation therefore
crosses the ≡CM boundary at `(3,4)` while preserving UNSAT status.

The local report is
`/tmp/candidate_b_step0_option_c/step0_option_c_comparison.json`. It is a
regenerable temporary output, not a tracked artifact. Repair enumeration was
not run and remains unauthorized pending review of this Step 0 classification.
