# Atlas Summary

## Headline

- atlas_schema_version: `1`
- cases_total: `32`
- SAT: `30`
- UNSAT: `2`
- UNKNOWN: `0`

## Runtime

- solver_path: `/opt/homebrew/Cellar/cadical/3.0.0/bin/cadical`
- solver_version_raw: `3.0.0`
- solver_version: `3.0.0`
- solver_sha256: `eee5786b12f606ed94339c128156e568b523fa12a2e3870774d19a1b3725988e`
- python_version: `3.9.6`
- platform: `macOS-15.6.1-arm64-arm-64bit`
- git_commit: `07609341304a149de5f47660514ccee9f4d614a9`

## Symmetry classes

- mode: `none`
- symmetry_unsafe_axioms: `[]`
- equivalence classes: `32`
- UNSAT classes: `2`
- symmetry_check: enabled=`False` checked_k=`0` mismatches=`0`
- checked_cases: `[]`
- representatives (32): `case_00000`, `case_00001`, `case_00010`, `case_00011`, `case_00100`, `case_00101`, `case_00110`, `case_00111`, `case_01000`, `case_01001`, `case_01010`, `case_01011`, `case_01100`, `case_01101`, `case_01110`, `case_01111`, `case_10000`, `case_10001`, `case_10010`, `case_10011`, `case_10100`, `case_10101`, `case_10110`, `case_10111`, `case_11000`, `case_11001`, `case_11010`, `case_11011`, `case_11100`, `case_11101`, `case_11110`, `case_11111`

## Pruning

- mode: `none`
- solver_calls: `32`
- solver_calls_avoided: `0`
- pruned_sat: `0`
- pruned_unsat: `0`
- oracle_sat_inferred: `0`
- oracle_unsat_inferred: `0`

## UNSAT cases

- `case_11101` solved=`True` on=['asymm', 'un', 'minlib', 'no_cycle4']
  - mus(size=4): ['asymm', 'un', 'minlib', 'no_cycle4']
  - mcs(remove=1): ['asymm']
- `case_11111` solved=`True` on=['asymm', 'un', 'minlib', 'no_cycle3', 'no_cycle4']
  - mus(size=4): ['asymm', 'un', 'minlib', 'no_cycle4']
  - mcs(remove=1): ['asymm']

## Closest SAT cases

- `case_11110` on_size=4 solved=`True` on=['asymm', 'un', 'minlib', 'no_cycle3']
- `case_11011` on_size=4 solved=`True` on=['asymm', 'un', 'no_cycle3', 'no_cycle4']
- `case_10111` on_size=4 solved=`True` on=['asymm', 'minlib', 'no_cycle3', 'no_cycle4']
- `case_01111` on_size=4 solved=`True` on=['un', 'minlib', 'no_cycle3', 'no_cycle4']
- `case_11100` on_size=3 solved=`True` on=['asymm', 'un', 'minlib']

## Class frontier

- `eq_28800e6a76f6f425` rep=`case_11101` orbit=1 status={'UNSAT': 1}
- `eq_e6fe01eca2dea498` rep=`case_11111` orbit=1 status={'UNSAT': 1}

## Frontier note

UNSAT case -> one-step SAT repair candidate via MCS:
- `case_11101` --remove ['asymm']--> `case_01101` (`sat_mask=22`)
- `case_11111` --remove ['asymm']--> `case_01111` (`sat_mask=30`)
