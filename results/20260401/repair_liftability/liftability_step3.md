# Step 3: Local Minimality Checks

**Generated:** 2026-03-31T15:46:30.763714+00:00  
**Solver:** cadical  
**Outcome:** A — All repairs remain locally minimal in both neighboring cases. Repair persistence AND local-minimality preservation confirmed. Candidate A is substantially weakened in the tested neighboring cases.

## Scope note

no_cycle3 and no_cycle4 are treated as local-rationality approximations, not full SocialAcyclic. Conclusions are valid only within that restricted local-rationality family. See docs/no_cycle_interpretation_note.md and docs/axiom_semantics_scaling.md.

## Summary

| Item | Count |
|------|-------|
| Step 2 SAT rows consumed | 16 |
| Element-level checks emitted | 16 |
| Aggregate rows emitted | 16 |

### By target case

| Target | Aggregate rows | Locally minimal | Not locally minimal |
|--------|---------------|-----------------|---------------------|
| `n2_m5` | 8 | 8 | 0 |
| `n3_m4` | 8 | 8 | 0 |

## Aggregate result table

| # | Base package | MCS R | Target | |R| | SAT checks | UNSAT checks | Locally minimal | Witness failures |
|---|-------------|-------|--------|-----|------------|--------------|-----------------|------------------|
| 1 | `asymm+un+minlib+no_cycle4` | `no_cycle4` | `n2_m5` | 1 | 0 | 1 | ✓ | — |
| 2 | `asymm+un+minlib+no_cycle4` | `no_cycle4` | `n3_m4` | 1 | 0 | 1 | ✓ | — |
| 3 | `asymm+un+minlib+no_cycle4` | `minlib` | `n2_m5` | 1 | 0 | 1 | ✓ | — |
| 4 | `asymm+un+minlib+no_cycle4` | `minlib` | `n3_m4` | 1 | 0 | 1 | ✓ | — |
| 5 | `asymm+un+minlib+no_cycle4` | `un` | `n2_m5` | 1 | 0 | 1 | ✓ | — |
| 6 | `asymm+un+minlib+no_cycle4` | `un` | `n3_m4` | 1 | 0 | 1 | ✓ | — |
| 7 | `asymm+un+minlib+no_cycle4` | `asymm` | `n2_m5` | 1 | 0 | 1 | ✓ | — |
| 8 | `asymm+un+minlib+no_cycle4` | `asymm` | `n3_m4` | 1 | 0 | 1 | ✓ | — |
| 9 | `asymm+un+minlib+no_cycle3+no_cycle4` | `no_cycle4` | `n2_m5` | 1 | 0 | 1 | ✓ | — |
| 10 | `asymm+un+minlib+no_cycle3+no_cycle4` | `no_cycle4` | `n3_m4` | 1 | 0 | 1 | ✓ | — |
| 11 | `asymm+un+minlib+no_cycle3+no_cycle4` | `minlib` | `n2_m5` | 1 | 0 | 1 | ✓ | — |
| 12 | `asymm+un+minlib+no_cycle3+no_cycle4` | `minlib` | `n3_m4` | 1 | 0 | 1 | ✓ | — |
| 13 | `asymm+un+minlib+no_cycle3+no_cycle4` | `un` | `n2_m5` | 1 | 0 | 1 | ✓ | — |
| 14 | `asymm+un+minlib+no_cycle3+no_cycle4` | `un` | `n3_m4` | 1 | 0 | 1 | ✓ | — |
| 15 | `asymm+un+minlib+no_cycle3+no_cycle4` | `asymm` | `n2_m5` | 1 | 0 | 1 | ✓ | — |
| 16 | `asymm+un+minlib+no_cycle3+no_cycle4` | `asymm` | `n3_m4` | 1 | 0 | 1 | ✓ | — |

## Element-level checks

| Base package | MCS R | Target | r removed | Test package | Status |
|-------------|-------|--------|-----------|-------------|--------|
| `asymm+un+minlib+no_cycle4` | `no_cycle4` | `n2_m5` | `no_cycle4` | `asymm+un+minlib+no_cycle4` | **UNSAT** |
| `asymm+un+minlib+no_cycle4` | `no_cycle4` | `n3_m4` | `no_cycle4` | `asymm+un+minlib+no_cycle4` | **UNSAT** |
| `asymm+un+minlib+no_cycle4` | `minlib` | `n2_m5` | `minlib` | `asymm+un+minlib+no_cycle4` | **UNSAT** |
| `asymm+un+minlib+no_cycle4` | `minlib` | `n3_m4` | `minlib` | `asymm+un+minlib+no_cycle4` | **UNSAT** |
| `asymm+un+minlib+no_cycle4` | `un` | `n2_m5` | `un` | `asymm+un+minlib+no_cycle4` | **UNSAT** |
| `asymm+un+minlib+no_cycle4` | `un` | `n3_m4` | `un` | `asymm+un+minlib+no_cycle4` | **UNSAT** |
| `asymm+un+minlib+no_cycle4` | `asymm` | `n2_m5` | `asymm` | `asymm+un+minlib+no_cycle4` | **UNSAT** |
| `asymm+un+minlib+no_cycle4` | `asymm` | `n3_m4` | `asymm` | `asymm+un+minlib+no_cycle4` | **UNSAT** |
| `asymm+un+minlib+no_cycle3+no_cycle4` | `no_cycle4` | `n2_m5` | `no_cycle4` | `asymm+un+minlib+no_cycle3+no_cycle4` | **UNSAT** |
| `asymm+un+minlib+no_cycle3+no_cycle4` | `no_cycle4` | `n3_m4` | `no_cycle4` | `asymm+un+minlib+no_cycle3+no_cycle4` | **UNSAT** |
| `asymm+un+minlib+no_cycle3+no_cycle4` | `minlib` | `n2_m5` | `minlib` | `asymm+un+minlib+no_cycle3+no_cycle4` | **UNSAT** |
| `asymm+un+minlib+no_cycle3+no_cycle4` | `minlib` | `n3_m4` | `minlib` | `asymm+un+minlib+no_cycle3+no_cycle4` | **UNSAT** |
| `asymm+un+minlib+no_cycle3+no_cycle4` | `un` | `n2_m5` | `un` | `asymm+un+minlib+no_cycle3+no_cycle4` | **UNSAT** |
| `asymm+un+minlib+no_cycle3+no_cycle4` | `un` | `n3_m4` | `un` | `asymm+un+minlib+no_cycle3+no_cycle4` | **UNSAT** |
| `asymm+un+minlib+no_cycle3+no_cycle4` | `asymm` | `n2_m5` | `asymm` | `asymm+un+minlib+no_cycle3+no_cycle4` | **UNSAT** |
| `asymm+un+minlib+no_cycle3+no_cycle4` | `asymm` | `n3_m4` | `asymm` | `asymm+un+minlib+no_cycle3+no_cycle4` | **UNSAT** |

## Interpretation

**Outcome A:** All repairs remain locally minimal in both neighboring cases. Repair persistence AND local-minimality preservation confirmed. Candidate A is substantially weakened in the tested neighboring cases.

- All repairs persist (SAT, Step 2) and are locally minimal (Step 3) in both `(2,5)` and `(3,4)` under the restricted local-rationality family.
- This weakens Candidate A for this family and these neighboring cases.
- Consider pivoting to Candidate B (encoding sensitivity) or introducing a stronger rationality encoding to extend the experiment.

All conclusions must be interpreted within the local-rationality family defined by `no_cycle3` and `no_cycle4`. Do **not** extend claims to full `SocialAcyclic`.

See `docs/no_cycle_interpretation_note.md` and `docs/axiom_semantics_scaling.md`.
