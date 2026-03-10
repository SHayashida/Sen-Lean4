# Human-readable SAT rule sketch

- case_id: `case_10001`
- status: `SAT`
- axioms_on: `asymm, no_cycle4`
- model true vars: `0` (p-vars: `0`, aux-vars: `0`)

## Variable semantics

- `p_var` (`1..n_p_vars`): social strict preference bit `P[p,a,b]`.
- `aux_var` (`n_p_vars+1..`): auxiliary encoding bits (e.g., MINLIB selectors).
- profile index convention: `p = r0 * nranks + r1`.

## Heuristic triviality scores

- `dictatorship_score_voter0`: fraction of `(p,a,b)` where social bit equals voter0 strict preference.
- `dictatorship_score_voter1`: fraction of `(p,a,b)` where social bit equals voter1 strict preference.
- `neutrality_violation_count` (heuristic): ordered pairs whose support differs from modal support.
- `pair_constancy_score`: average per-pair constancy over profiles (`1.0` means constant by pair).
- `distinct_social_outcomes`: number of distinct social edge signatures across profiles.

- dictatorship_score_voter0: `0.5000`
- dictatorship_score_voter1: `0.5000`
- neutrality_violation_count: `0` / `12`
- pair_constancy_score: `1.0000`
- distinct_social_outcomes: `1`
- constant_function_flag: `True`
- dictator_like_voter0_flag: `False`
- dictator_like_voter1_flag: `False`

## Profile samples

Showing first `20` profiles (out of `576`).

- `p=0` (`r0=[0,1,2,3]`, `r1=[0,1,2,3]`) -> social edges: (none)
- `p=1` (`r0=[0,1,2,3]`, `r1=[0,1,3,2]`) -> social edges: (none)
- `p=2` (`r0=[0,1,2,3]`, `r1=[0,2,1,3]`) -> social edges: (none)
- `p=3` (`r0=[0,1,2,3]`, `r1=[0,2,3,1]`) -> social edges: (none)
- `p=4` (`r0=[0,1,2,3]`, `r1=[0,3,1,2]`) -> social edges: (none)
- `p=5` (`r0=[0,1,2,3]`, `r1=[0,3,2,1]`) -> social edges: (none)
- `p=6` (`r0=[0,1,2,3]`, `r1=[1,0,2,3]`) -> social edges: (none)
- `p=7` (`r0=[0,1,2,3]`, `r1=[1,0,3,2]`) -> social edges: (none)
- `p=8` (`r0=[0,1,2,3]`, `r1=[1,2,0,3]`) -> social edges: (none)
- `p=9` (`r0=[0,1,2,3]`, `r1=[1,2,3,0]`) -> social edges: (none)
- `p=10` (`r0=[0,1,2,3]`, `r1=[1,3,0,2]`) -> social edges: (none)
- `p=11` (`r0=[0,1,2,3]`, `r1=[1,3,2,0]`) -> social edges: (none)
- `p=12` (`r0=[0,1,2,3]`, `r1=[2,0,1,3]`) -> social edges: (none)
- `p=13` (`r0=[0,1,2,3]`, `r1=[2,0,3,1]`) -> social edges: (none)
- `p=14` (`r0=[0,1,2,3]`, `r1=[2,1,0,3]`) -> social edges: (none)
- `p=15` (`r0=[0,1,2,3]`, `r1=[2,1,3,0]`) -> social edges: (none)
- `p=16` (`r0=[0,1,2,3]`, `r1=[2,3,0,1]`) -> social edges: (none)
- `p=17` (`r0=[0,1,2,3]`, `r1=[2,3,1,0]`) -> social edges: (none)
- `p=18` (`r0=[0,1,2,3]`, `r1=[3,0,1,2]`) -> social edges: (none)
- `p=19` (`r0=[0,1,2,3]`, `r1=[3,0,2,1]`) -> social edges: (none)
