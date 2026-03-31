# Step 2: Repair Liftability — Apply Repairs to Larger Cases

**Generated:** 2026-03-31T15:35:33.321668+00:00  
**Source triples:** `results/20260401/repair_liftability/base_triples.json`  
**Solver:** cadical  

## Scope note

no_cycle3 and no_cycle4 are treated as local-rationality approximations, not full SocialAcyclic. Results for (2,5) are valid only within that restricted local-rationality family. See docs/no_cycle_interpretation_note.md and docs/axiom_semantics_scaling.md.

## Summary

| Item | Count |
|------|-------|
| Step 1 triples consumed | 8 |
| Step 2 rows emitted | 16 |

### By target case

| Target | Total | SAT | UNSAT |
|--------|-------|-----|-------|
| `n2_m5` | 8 | 8 | 0 |
| `n3_m4` | 8 | 8 | 0 |

## Result table

| # | Base package | MCS R_i | Repaired A\\R_i | (2,5) | (3,4) |
|---|-------------|---------|----------------|-------|-------|
| 1 | `asymm+un+minlib+no_cycle4` | `no_cycle4` | `asymm+un+minlib` | SAT | SAT |
| 2 | `asymm+un+minlib+no_cycle4` | `minlib` | `asymm+un+no_cycle4` | SAT | SAT |
| 3 | `asymm+un+minlib+no_cycle4` | `un` | `asymm+minlib+no_cycle4` | SAT | SAT |
| 4 | `asymm+un+minlib+no_cycle4` | `asymm` | `un+minlib+no_cycle4` | SAT | SAT |
| 5 | `asymm+un+minlib+no_cycle3+no_cycle4` | `no_cycle4` | `asymm+un+minlib+no_cycle3` | SAT | SAT |
| 6 | `asymm+un+minlib+no_cycle3+no_cycle4` | `minlib` | `asymm+un+no_cycle3+no_cycle4` | SAT | SAT |
| 7 | `asymm+un+minlib+no_cycle3+no_cycle4` | `un` | `asymm+minlib+no_cycle3+no_cycle4` | SAT | SAT |
| 8 | `asymm+un+minlib+no_cycle3+no_cycle4` | `asymm` | `un+minlib+no_cycle3+no_cycle4` | SAT | SAT |

## Interpretation

- **SAT** in a larger case: the repair persists. Proceed to Step 3 to check local minimality.
- **UNSAT** in a larger case: strong non-liftability for this repair in this family size.

All results must be interpreted within the local-rationality family defined by `no_cycle3` and `no_cycle4`. Do **not** extend claims to full `SocialAcyclic` unless a stronger rationality encoding is introduced in later work.

See `docs/no_cycle_interpretation_note.md` and `docs/axiom_semantics_scaling.md`.
