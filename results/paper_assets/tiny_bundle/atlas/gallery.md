# SAT Gallery

This gallery lists deterministic SAT witnesses selected from atlas outputs under non-triviality heuristics.

## Reproduce

```bash
python3 scripts/build_sat_gallery.py --atlas-outdir <atlas_outdir> --top-k 5 --min-k 1
```

## Selected entries

| case_id | axioms_on | distinct_social_outcomes | dictatorship_score_max | model_validated |
|---|---|---:|---:|---:|
| `case_01000` | `un` | 219 | 0.7500 | True |
| `case_01001` | `un,no_cycle4` | 219 | 0.7500 | True |
| `case_11000` | `asymm,un` | 219 | 0.7500 | True |

## Entry `case_01000`

- axioms_on: `un`
- equiv_class_id: `eq_67a818cc31cfe149`
- orbit_size: `1`
- representative_case: `case_01000`
- model_validated: `True`
- non_trivial: `True`
- metrics: distinct=`219`, dict_max=`0.7500`, constant_rate=`0.0000`
- nontriviality: included=`passes_non_triviality_thresholds`, excluded=`(none)`
- files: rule=`case_01000/rule.md`, model=`case_01000/model.json`, rule_card_md=`case_01000/rule_card.md`, rule_card_tex=`case_01000/rule_card.tex`, cnf=`case_01000/sen24.cnf`, manifest=`case_01000/sen24.manifest.json`

### Rule excerpt (first 15 lines)

```text
# Human-readable SAT rule sketch

- case_id: `case_01000`
- status: `SAT`
- axioms_on: `un`
- model true vars: `1728` (p-vars: `1728`, aux-vars: `0`)

## Variable semantics

- `p_var` (`1..n_p_vars`): social strict preference bit `P[p,a,b]`.
- `aux_var` (`n_p_vars+1..`): auxiliary encoding bits (e.g., MINLIB selectors).
- profile index convention: `p = r0 * nranks + r1`.

## Heuristic triviality scores

```

## Entry `case_01001`

- axioms_on: `un, no_cycle4`
- equiv_class_id: `eq_5ad2841192c954f8`
- orbit_size: `1`
- representative_case: `case_01001`
- model_validated: `True`
- non_trivial: `True`
- metrics: distinct=`219`, dict_max=`0.7500`, constant_rate=`0.0000`
- nontriviality: included=`passes_non_triviality_thresholds`, excluded=`(none)`
- files: rule=`case_01001/rule.md`, model=`case_01001/model.json`, rule_card_md=`case_01001/rule_card.md`, rule_card_tex=`case_01001/rule_card.tex`, cnf=`case_01001/sen24.cnf`, manifest=`case_01001/sen24.manifest.json`

### Rule excerpt (first 15 lines)

```text
# Human-readable SAT rule sketch

- case_id: `case_01001`
- status: `SAT`
- axioms_on: `un, no_cycle4`
- model true vars: `1728` (p-vars: `1728`, aux-vars: `0`)

## Variable semantics

- `p_var` (`1..n_p_vars`): social strict preference bit `P[p,a,b]`.
- `aux_var` (`n_p_vars+1..`): auxiliary encoding bits (e.g., MINLIB selectors).
- profile index convention: `p = r0 * nranks + r1`.

## Heuristic triviality scores

```

## Entry `case_11000`

- axioms_on: `asymm, un`
- equiv_class_id: `eq_763efde5da8ab7f0`
- orbit_size: `1`
- representative_case: `case_11000`
- model_validated: `True`
- non_trivial: `True`
- metrics: distinct=`219`, dict_max=`0.7500`, constant_rate=`0.0000`
- nontriviality: included=`passes_non_triviality_thresholds`, excluded=`(none)`
- files: rule=`case_11000/rule.md`, model=`case_11000/model.json`, rule_card_md=`case_11000/rule_card.md`, rule_card_tex=`case_11000/rule_card.tex`, cnf=`case_11000/sen24.cnf`, manifest=`case_11000/sen24.manifest.json`

### Rule excerpt (first 15 lines)

```text
# Human-readable SAT rule sketch

- case_id: `case_11000`
- status: `SAT`
- axioms_on: `asymm, un`
- model true vars: `1728` (p-vars: `1728`, aux-vars: `0`)

## Variable semantics

- `p_var` (`1..n_p_vars`): social strict preference bit `P[p,a,b]`.
- `aux_var` (`n_p_vars+1..`): auxiliary encoding bits (e.g., MINLIB selectors).
- profile index convention: `p = r0 * nranks + r1`.

## Heuristic triviality scores

```
