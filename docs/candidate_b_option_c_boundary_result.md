# Candidate B: Option C Voter-Boundary Result (M2.1)

## Purpose

This note records the Option C Step 0 boundary result for `(3,4)`. Option C is
an exploratory voter-dimension comparison; it is not the Option D positive
track and does not authorize repair enumeration.

## Relation to Option D

Option D is the completed positive track. It shows that M1.5
repair-presentation non-canonicity persists from `(2,4)` to `(2,5)` under
clause-multiset equivalence (≡CM) while the voter count remains two.

Option C asks the separate voter-dimension question: what happens when the
split representation must select two witnesses among three voters?

## Step 0 Strategy

The bundled package is the repository's existing `(3,4)` parametric `minlib`
encoding using `pair_selectors_v1`.

The exploratory split package uses the transport map:

```text
π(minlib)    = {selected_decisive_left, selected_decisive_right}
π(asymm)     = {asymm}
π(un)        = {un}
π(no_cycle3) = {no_cycle3}
π(no_cycle4) = {no_cycle4}
```

Both split levers share one witness-pair selector bank. They use separate
left/right decisive-selector banks so that each lever exposes its witness role
independently.

## Result

For `(3,4)`:

| Measurement | Bundled | Split |
| --- | ---: | ---: |
| SAT status | `UNSAT` | `UNSAT` |
| Variables | 165,927 | 165,939 |
| Clauses | 1,347,847 | 1,513,735 |

The Step 0 classification is `sat_equiv_only`. SAT/UNSAT status agrees, but
clause-multiset equivalence is false.

## Structural Difference

The split side adds:

- 12 variables;
- 165,888 binary implication clauses.

At `(3,4)`, voter 1 can be the right witness in pair `(0,1)` and the left
witness in pair `(1,2)`. The split representation therefore gives voter 1
distinct left/right role-specific decisive-selector series. These selectors and
their implication clauses have no one-to-one counterpart in bundled `minlib`.

The distinct-variable count, clause count, and clause-length histogram all
differ. These are invariants under variable renaming, so no bijection `ρ` can
make the two clause multisets equal.

## Interpretation

Status transfers at `(3,4)`, but the M1.5-style ≡CM shield does not. Therefore
the strong M1.5-style, ≡CM-protected repair-representation non-canonicity claim
is not authorized for Option C at `(3,4)`.

This is a voter-dimension representation boundary, not an Option D regression.
The evidence supports the narrower statement that the M1.5 witness class
transfers cleanly along the two-voter alternative-expansion track but does not
automatically transfer along the voter-dimension track.

## Gate

Option C repair enumeration and MCS enumeration remain unauthorized after the
`sat_equiv_only` classification. This Step 0 result must not be used as a basis
for an ≡CM-protected repair claim.

## Scope

`no_cycle3 ∧ no_cycle4` is treated as a local-rationality family and is not full
`SocialAcyclic` at family scale.

M2 is unchanged. No M2 theorem or paper claim is modified. The sen24 CNF is not
a family-level CNF certificate.

## Artifact Pointers

- [`scripts/exploration/candidate_b/option_c_encoder.py`](../scripts/exploration/candidate_b/option_c_encoder.py)
- [`scripts/exploration/candidate_b/step0_equiv_check_option_c.py`](../scripts/exploration/candidate_b/step0_equiv_check_option_c.py)
- `/tmp/candidate_b_step0_option_c/step0_option_c_comparison.json`

The `/tmp` report is a local, regenerable output and is not a tracked
repository artifact.
