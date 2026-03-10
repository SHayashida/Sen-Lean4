# Rule Card: `case_11000`

## Key metrics

- axioms_on: `asymm, un`
- model_validated: `True`
- distinct_social_outcomes: `219`
- dictatorship_score_max: `0.7500`
- constant_function_rate: `0.0000`
- neutrality_violation_count: `0`

## Non-triviality report

- passes_non_triviality: `True`
- included_reasons: `passes_non_triviality_thresholds`
- excluded_reasons: `(none)`

## Profile witnesses

### Witness 1
- profile_id: `0`; tags: `non_constant_witness`
- voter0 ranking: `[0,1,2,3]`
- voter1 ranking: `[0,1,2,3]`
- social edges: `0>1, 0>2, 0>3, 1>2, 1>3, 2>3`
- differs_from_voter0: `False`, differs_from_voter1: `False`

### Witness 2
- profile_id: `1`; tags: `non_constant_witness, non_dictatorship_voter0_witness, non_dictatorship_voter1_witness`
- voter0 ranking: `[0,1,2,3]`
- voter1 ranking: `[0,1,3,2]`
- social edges: `0>1, 0>2, 0>3, 1>2, 1>3`
- differs_from_voter0: `True`, differs_from_voter1: `True`
