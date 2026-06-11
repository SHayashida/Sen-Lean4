# Step 1: Base-Case Repair Triples

**Generated:** 2026-03-31T15:06:46.820628+00:00  
**Base case:** n=2, m=4 (`n2_m4`)  
**Axiom family:** asymm, un, minlib, no_cycle3, no_cycle4  

## Scope note

no_cycle3 and no_cycle4 are treated as local-rationality approximations, not full SocialAcyclic. Candidate A evidence is valid only within that restricted local-rationality family. See docs/no_cycle_interpretation_note.md and docs/axiom_semantics_scaling.md.

## Summary

| Item | Count |
|------|-------|
| UNSAT base packages | 2 |
| Total minimal repairs | 8 |
| Emitted triples | 8 |

## Per-package detail

### `asymm+un+minlib+no_cycle4`

- Atlas case: `case_11101`
- Active levers: ['asymm', 'un', 'minlib', 'no_cycle4']
- Number of minimal repairs: 4
- Repaired packages (A \ R_i):

  - `asymm+un+minlib`
  - `asymm+un+no_cycle4`
  - `asymm+minlib+no_cycle4`
  - `un+minlib+no_cycle4`

### `asymm+un+minlib+no_cycle3+no_cycle4`

- Atlas case: `case_11111`
- Active levers: ['asymm', 'un', 'minlib', 'no_cycle3', 'no_cycle4']
- Number of minimal repairs: 4
- Repaired packages (A \ R_i):

  - `asymm+un+minlib+no_cycle3`
  - `asymm+un+no_cycle3+no_cycle4`
  - `asymm+minlib+no_cycle3+no_cycle4`
  - `un+minlib+no_cycle3+no_cycle4`

## Triple listing

| # | Base package | MCS R_i | Repaired A\\R_i |
|---|-------------|---------|----------------|
| 1 | `asymm+un+minlib+no_cycle4` | `no_cycle4` | `asymm+un+minlib` |
| 2 | `asymm+un+minlib+no_cycle4` | `minlib` | `asymm+un+no_cycle4` |
| 3 | `asymm+un+minlib+no_cycle4` | `un` | `asymm+minlib+no_cycle4` |
| 4 | `asymm+un+minlib+no_cycle4` | `asymm` | `un+minlib+no_cycle4` |
| 5 | `asymm+un+minlib+no_cycle3+no_cycle4` | `no_cycle4` | `asymm+un+minlib+no_cycle3` |
| 6 | `asymm+un+minlib+no_cycle3+no_cycle4` | `minlib` | `asymm+un+no_cycle3+no_cycle4` |
| 7 | `asymm+un+minlib+no_cycle3+no_cycle4` | `un` | `asymm+minlib+no_cycle3+no_cycle4` |
| 8 | `asymm+un+minlib+no_cycle3+no_cycle4` | `asymm` | `un+minlib+no_cycle3+no_cycle4` |

## Interpretation scope

All triples in this file are valid base inputs for Step 2 (liftability checks) under the restricted local-rationality interpretation of `no_cycle3` and `no_cycle4`.
Do **not** interpret results from these triples as evidence about full `SocialAcyclic` unless a stronger rationality encoding is added in later work.

See `docs/no_cycle_interpretation_note.md` and `docs/axiom_semantics_scaling.md`.
