# M2.1 Two-Sided Status Summary

## 1. Purpose

This note summarizes the current M2.1 state after completion of the Option D
positive track and the Option C voter-dimension boundary track.

## 2. Core Question

M2.1 tests whether the M1.5 repair-candidate representation non-canonicity
persists in two neighboring cases. The comparison distinguishes the tested
two-voter alternative-expansion case `(2,5)` from the tested voter-dimension
case `(3,4)`.

## 3. Positive Side: Option D / `(2,5)`

Option D tests the two-voter alternative-expansion direction.

- Case: `(2,5)`
- Step 0 classification: `equiv_cm_persists`
- Repair classification: `noncanonical_persists`

The interpretation is strong: increasing the number of alternatives while
holding the two-voter witness structure fixed preserves the M1.5
clause-multiset-equivalence (≡CM) shield and the associated
repair-representation non-canonicity.

## 4. Boundary Side: Option C / `(3,4)`

Option C tests the voter-dimension direction at `(3,4)`.

- Bundled status: `UNSAT`
- Split status: `UNSAT`
- Step 0 classification: `sat_equiv_only`
- Clause-multiset equivalence: `false`
- Structural difference: 12 additional variables and 165,888 additional
  clauses on the split side

Status survives the Option C comparison, but the M1.5 ≡CM shield does not.
Role-specific selector machinery, particularly the separate left/right
decisive-selector series for voter 1, introduces unmatched variables and
clauses.

## 5. Current Conclusion

In the tested `(2,5)` case, the M1.5 witness class transfers cleanly along the
two-voter alternative-expansion direction. In the tested `(3,4)` case, it does
not automatically transfer along the voter-dimension direction.

This is a two-sided M2.1 result, not a failure: Option D identifies where the
strong witness transfers in the tested `(2,5)` setting, while Option C
identifies where, in the tested `(3,4)` setting, the
clause-multiset-equivalence control stops.

## 6. Scope Caveat

The current evidence is local-rationality only:
`no_cycle3 ∧ no_cycle4` is not full `SocialAcyclic` at family scale.

The sen24 CNF is not a family-level CNF certificate. M2 remains unchanged; no
M2 theorem or paper claim is altered by the M2.1 witness results.

## 7. Artifact Pointers

Result and design notes:

- [Option D positive-track result](candidate_b_option_d_positive_track.md)
- [Option C voter-boundary result](candidate_b_option_c_boundary_result.md)
- [Parametric split design](candidate_b_parametric_split_design.md)
- [Encoding-sensitivity witness class](candidate_b_encoding_sensitivity.md)

Relevant exploratory scripts:

- [`scripts/exploration/candidate_b/option_d_encoder.py`](../scripts/exploration/candidate_b/option_d_encoder.py)
- [`scripts/exploration/candidate_b/step0_equiv_check_option_d.py`](../scripts/exploration/candidate_b/step0_equiv_check_option_d.py)
- [`scripts/exploration/candidate_b/enumerate_option_d_repairs.py`](../scripts/exploration/candidate_b/enumerate_option_d_repairs.py)
- [`scripts/exploration/candidate_b/option_c_encoder.py`](../scripts/exploration/candidate_b/option_c_encoder.py)
- [`scripts/exploration/candidate_b/step0_equiv_check_option_c.py`](../scripts/exploration/candidate_b/step0_equiv_check_option_c.py)

## 8. Not Yet Authorized

- Option C repair enumeration remains unauthorized.
- Promotion to top-level `scripts/` remains unauthorized.
- The paper scaffold has not started.
- Production generator and `encoding/schema.py` changes are not authorized.

## 9. Next Decision

The next explicit decision is between:

1. Freeze the current two-sided M2.1 results and begin a paper scaffold.
2. Separately authorize an exploratory Option C repair comparison under the
   weaker `sat_equiv_only` framing, for use as an appendix rather than as an
   ≡CM-protected flagship result.

Until that decision is made, the strong M2.1 claim rests on Option D, and no
Option C repair enumeration should run.
