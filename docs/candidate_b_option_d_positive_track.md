# Candidate B: Option D Positive-Track Result (M2.1)

## 1. Purpose

This note records the M2.1 Option D positive-track result for the
`(2,m)`-restricted two-witness split. It consolidates the reviewed Step 0
clause-multiset-equivalence check and the subsequent raw lever-level repair
enumeration.

**Boundary track:** See [docs/candidate_b_option_c_boundary_plan.md](candidate_b_option_c_boundary_plan.md) for the pending Option C / `(3,4)` plan.

## 2. Scope

The result covers:

- `(2,4)` as the M1.5 base-case control;
- `(2,5)` as the first alternative-expansion family case.

The result does not cover:

- Option C;
- `(3,4)`;
- transfer along the voter dimension;
- full `SocialAcyclic`.

The positive track holds the voter count fixed at two and increases only the
number of alternatives.

## 3. Encoder Structure

Option D uses the exploratory legacy-style `sel0`/`sel1` two-series encoder
under [`scripts/exploration/candidate_b/`](../scripts/exploration/candidate_b/).
Bundled `minlib` emits both selector series, while the split package exposes
them separately as `decisive_voter0` and `decisive_voter1`.

The construction has the following controls:

- `pair_selectors_v1` is not used;
- no pair-selector variables or pair-selection clauses are introduced;
- `encoding/schema.py` is unchanged;
- bundled and split packages use the same `sel0`/`sel1` variable basis.

Because the bundled `minlib` clauses are exactly the union of the two split
decisive series over this shared variable basis, the identity variable map
`ρ(v) = v` witnesses clause-multiset equivalence (≡CM).

## 4. Step 0 Equivalence Result

Both authorized cases preserve the M1.5 equivalence control:

| Case | Classification | Status | Verified renaming | Bundled `minlib` split |
| --- | --- | --- | --- | --- |
| `(2,4)` | `equiv_cm_persists` | UNSAT/UNSAT | identity `ρ` | `13,826 = 6,913 + 6,913` |
| `(2,5)` | `equiv_cm_persists` | UNSAT/UNSAT | identity `ρ` | `576,002 = 288,001 + 288,001` |

The two summands are the clause counts for `decisive_voter0` and
`decisive_voter1`, respectively. The verified identity `ρ`, rather than clause
counts alone, establishes ≡CM.

## 5. Repair Enumeration Result

For both `(2,4)` and `(2,5)`, the raw lever-level inclusion-minimal repair
families are identical:

| Representation | Raw inclusion-minimal repairs |
| --- | --- |
| Bundled | `{asymm}`, `{un}`, `{minlib}`, `{no_cycle4}` |
| Split | `{asymm}`, `{un}`, `{decisive_voter0}`, `{decisive_voter1}`, `{no_cycle4}` |
| Transported bundled under `π` | `{asymm}`, `{un}`, `{decisive_voter0, decisive_voter1}`, `{no_cycle4}` |

The transport map sends `minlib` to
`{decisive_voter0, decisive_voter1}` and sends every shared lever to its
singleton counterpart. It is a lever correspondence and repair-transport map,
not a semantic equivalence claim.

For each case:

- `transported_bundled_repairs == split_repairs` is `false`;
- the classification is `noncanonical_persists`.

## 6. Interpretation

The Option D positive track establishes that M1.5 repair-presentation
non-canonicity persists from `(2,4)` to `(2,5)` under clause-multiset
equivalence.

This divergence is not an encoding-strength artifact: bundled and split
packages have verified ≡CM under the identity `ρ`. The difference occurs at
repair-candidate representation granularity. The bundled singleton repair
`{minlib}` transports to the two-lever set
`{decisive_voter0, decisive_voter1}`, while the split representation exposes
each person-specific lever as a separate singleton repair.

The result is limited to the two-voter alternative-expansion family. It does not
show that the same split representation or repair pattern transfers when the
number of voters increases.

## 7. Boundary Still Open

Option C and `(3,4)` remain open as the voter-dimension boundary track. The
Option D result does not settle whether a person-specific split representation
can preserve ≡CM, or preserve the same repair behavior, when the voter number
increases.

No Option C encoder or repair enumeration is part of this result.

## 8. Artifact Pointers

The exploratory implementation is:

- [`scripts/exploration/candidate_b/option_d_encoder.py`](../scripts/exploration/candidate_b/option_d_encoder.py)
- [`scripts/exploration/candidate_b/step0_equiv_check_option_d.py`](../scripts/exploration/candidate_b/step0_equiv_check_option_d.py)
- [`scripts/exploration/candidate_b/enumerate_option_d_repairs.py`](../scripts/exploration/candidate_b/enumerate_option_d_repairs.py)

The local runs produced:

- `/tmp/candidate_b_step0_option_d/step0_option_d_comparison.json`
- `/tmp/candidate_b_option_d_repairs/option_d_repairs.json`

These `/tmp` reports are local, regenerable outputs and are not tracked
repository artifacts.

## 9. Scope Caveat

`no_cycle3 ∧ no_cycle4` is treated as a local-rationality family and is not full
`SocialAcyclic` at family scale.

This Option D witness-layer result does not alter M2, does not modify or extend
any M2 theorem or paper claim, and does not make the Sen24 CNF witness a
family-level CNF certificate.
