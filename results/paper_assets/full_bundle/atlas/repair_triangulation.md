# Repair Triangulation

This report compares enumerated `mcs_min_size`/`mcs_min_all` with an independent optimum baseline (bruteforce solver checks over axiom-drop subsets).

| case_id | optimum_drop_count | mcs_min_size | size_match | set_match |
|---|---:|---:|---:|---:|
| `case_11101` | 1 | 1 | True | True |
| `case_11111` | 1 | 1 | True | True |

## case_11101

- axioms_on: `asymm, un, minlib, no_cycle4`
- optimum_repairs: `[['asymm'], ['minlib'], ['no_cycle4'], ['un']]`
- mcs_min_all: `[['asymm'], ['minlib'], ['no_cycle4'], ['un']]`
- verdict: `size_match=True`, `set_match=True`

## case_11111

- axioms_on: `asymm, un, minlib, no_cycle3, no_cycle4`
- optimum_repairs: `[['asymm'], ['minlib'], ['no_cycle4'], ['un']]`
- mcs_min_all: `[['asymm'], ['minlib'], ['no_cycle4'], ['un']]`
- verdict: `size_match=True`, `set_match=True`
