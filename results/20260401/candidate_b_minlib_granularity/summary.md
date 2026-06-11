# Candidate B Summary

**Generated:** 2026-03-31T23:02:45.304033+00:00  
**Base case:** n=2, m=4 only  
**Scope note:** This Candidate B experiment stays inside the restricted local-rationality family defined by no_cycle3 and no_cycle4. It is not evidence about full SocialAcyclic. See docs/no_cycle_interpretation_note.md and docs/axiom_semantics_scaling.md.

## Comparison

- Representation A (bundled): `asymm, un, minlib, no_cycle3, no_cycle4`.
- Representation B (split): `asymm, un, decisive_voter0, decisive_voter1, no_cycle3, no_cycle4`.
- The main comparison stays entirely inside the current `no_cycle3` / `no_cycle4` local-rationality family.

## Logical relation

- Split `minlib` is classified as **logically equivalent** relative to bundled `minlib` at the base case.
- Detail: exact clause-multiset equivalence under the bundled→split mapping.
- Mapped bundled/split cases checked: `32`.

## Frontier

- Bundled UNSAT cases: `2`.
- Split UNSAT cases: `2`.
- Corresponding bundled→split mapped cases preserve status: `True`.
- Split one-sided decisive cases status counts: `{'SAT': 32}`.

## Repair explanation

- Cleanest witness: bundled `asymm+un+minlib+no_cycle4` versus split `asymm+un+decisive_voter0+decisive_voter1+no_cycle4`.
- Bundled minimal repairs: `no_cycle4, minlib, un, asymm`.
- Split minimal repairs: `no_cycle4, decisive_voter1, decisive_voter0, un, asymm`.
- This changes the repair explanation from a bundled liberalism repair to person-specific liberalism repairs.

## Candidate B assessment

- Candidate B concrete support: `True`.
- Classification: `granularity-sensitive under logical equivalence`.
- Evidence levels satisfied: `[1, 2, 3, 4]`.

## Conclusion

- The corresponding bundled and split packages are clause-set equivalent at the base case, so the observed repair difference is not explained by a stronger split encoding.
- The mapped UNSAT frontier is unchanged, but the repair explanation changes when `minlib` is exposed as `decisive_voter0` and `decisive_voter1`.
- This is direct Candidate B evidence inside the restricted local-rationality family.
