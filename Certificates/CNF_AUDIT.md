# Sen (n=2, m=4) CNF Audit Checklist

This repo encodes the Sen base case as a DIMACS CNF (`Certificates/sen24.cnf`) and checks UNSAT via an LRAT proof (`Certificates/sen24.lrat`) in Lean (`SocialChoiceAtlas/Sen/BaseCase24/SATSenCNF.lean`).

This document lists the **mechanical invariants** that must hold for the CNF generator output, and what the checker script enforces.

## 0) Files and tooling

- CNF generator: `scripts/gen_sen24_dimacs.py`
- CNF output: `Certificates/sen24.cnf`
- Manifest output: `Certificates/sen24.manifest.json` (schema + counts; CNF itself must be comment-free for Mathlib)
- Audit checker: `scripts/check_sen24_cnf.py`
- Lean checker: `SocialChoiceAtlas/Sen/BaseCase24/SATSenCNF.lean` (uses `lrat_proof` + `include_str`)

## 1) DIMACS well-formedness

- Header exists and is of the form `p cnf <nvars> <nclauses>`.
- Exactly `<nclauses>` clauses are present after stripping empty / `c` lines.
- Every clause line:
  - ends with a trailing `0`,
  - contains no other `0`,
  - contains only nonzero literals with `abs(lit) ≤ nvars`.
- Optional hygiene (warn if violated):
  - no repeated literal inside a clause,
  - no tautological clause containing both `x` and `-x`.

## 2) Schema invariants (must match spec)

Constants:
- Alternatives `ALT = {0,1,2,3}`.
- Rankings per voter: `24` permutations of `[0,1,2,3]` in **`itertools.permutations` lex order**.
- Profiles: `NPROFILES = 24^2 = 576` in order `p = r0*24 + r1` (r0-major).
- Ordered pairs `a≠b`: `NPAIRS = 12` with *fixed* order:
  - `[(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,0),(2,1),(2,3),(3,0),(3,1),(3,2)]`

Variable numbering:
- Main variables `s[p,a,b]` occupy DIMACS ids `1..6912` with:
  - `var_id(p,a,b) = 1 + p*NPAIRS + pair_index(a,b)`
- MINLIB selector vars occupy `6913..6936` (24 vars total):
  - 12 selectors for voter0 decisive pair + 12 selectors for voter1 decisive pair.

## 3) Clause categories and expected counts

Let `s[p,a,b]` be the Bool meaning “society strictly prefers `a` over `b` under profile `p`”.

1) **ASYMM** (asymmetry of strict relation)
- For all `p` and all ordered `(a,b)` in PAIRS:
  - `(¬s[p,a,b] ∨ ¬s[p,b,a])`
- Count: `576 * 12 = 6912`
- (Note: clauses are duplicated across `(a,b)` and `(b,a)`; this is intended here because it matches the audited spec.)

2) **UN** (unanimity / weak Pareto on strict relation)
- For all `p` and all ordered `(a,b)` in PAIRS:
  - if both voters prefer `a>b` in profile `p`, then `s[p,a,b]` must hold.
- CNF form: unit clause `(s[p,a,b])` for each true-unanimity instance.
- Count is data-dependent but for uniform rankings it equals `576*12/4 = 1728`.

3) **MINLIB** (minimal liberalism) using selectors (`selectors_v1`)
- `(∨_{(x,y)∈PAIRS} sel0(x,y)) ∧ (∨_{(z,w)∈PAIRS} sel1(z,w))`
- For each selector and each profile, enforce decisiveness by implication:
  - `sel0(x,y) → (if voter0 prefers x>y then s[p,x,y] else s[p,y,x])`
  - `sel1(z,w) → (if voter1 prefers z>w then s[p,z,w] else s[p,w,z])`
- CNF form:
  - 2 “at least one” clauses of length 12, and
  - `2 * 576 * 12 = 13824` binary implication clauses.
- Total MINLIB count: `13826`.

4) **NO_CYCLE3** (forbid all directed 3-cycles per profile)
- For all profiles `p` and all ordered distinct triples `(a,b,c)`:
  - `(¬s[p,a,b] ∨ ¬s[p,b,c] ∨ ¬s[p,c,a])`
- Count: `576 * P(4,3) = 576 * 24 = 13824`

5) **NO_CYCLE4** (forbid all directed 4-cycles per profile)
- For all profiles `p` and all ordered distinct quadruples `(a,b,c,d)`:
  - `(¬s[p,a,b] ∨ ¬s[p,b,c] ∨ ¬s[p,c,d] ∨ ¬s[p,d,a])`
- Count: `576 * P(4,4) = 576 * 24 = 13824`

## 4) Manifest invariants

`Certificates/sen24.manifest.json` must:
- match CNF header values (`nvars`, `nclauses`),
- record `pair_order`, `ranking_order`, `profile_order`, and `category_counts`,
- record `p_var_range` and `aux_var_range`,
- record `cnf_sha256` matching the CNF file.

## 5) How to run the audit

1. Regenerate CNF + manifest:
   - `python3 scripts/gen_sen24_dimacs.py`
2. Run the mechanical audit:
   - `python3 scripts/check_sen24_cnf.py Certificates/sen24.cnf --manifest Certificates/sen24.manifest.json`
3. (Optional) regenerate LRAT and re-check in Lean:
   - `cadical --lrat --no-binary Certificates/sen24.cnf Certificates/sen24.lrat`
   - `lake build SocialChoiceAtlas.Sen.BaseCase24.SATSenCNF`

