# SAT/LRAT Certificate Verification

This directory stores SAT proof artifacts for the Sen base case (`n=2`, `m=4`).
Verification is done in Lean via `Mathlib.Tactic.Sat.FromLRAT`.

## Files

- `sen24.cnf`: DIMACS CNF instance
- `sen24.lrat`: LRAT certificate (UNSAT proof trace)
- `sen24.manifest.json`: schema/count metadata for CNF audits
- `CNF_AUDIT.md`: audit checklist and invariants
- `atlas/case_11111/`: committed proof-carrying atlas UNSAT artifact

Policy:

- Keep baseline artifacts (`sen24.*`) immutable.
- Keep committed atlas proof artifacts to a single fixed case (`atlas/case_11111`) for CI stability.
- For other atlas cases, generate under `results/...` or `/tmp`; track reproducibility via hashes and reproduce command stored in each case `summary.json`.

## Regeneration and verification

1. Regenerate CNF + manifest:
   - `python3 scripts/gen_dimacs.py --n 2 --m 4 --axioms asymm,un,minlib,no_cycle3,no_cycle4`
   - (backward compatible) `python3 scripts/gen_sen24_dimacs.py`
2. Run structural audits:
   - `python3 scripts/check_sen24_cnf.py Certificates/sen24.cnf --manifest Certificates/sen24.manifest.json --strict-duplicates --fail-on-tautology`
3. Regenerate LRAT from CNF (example: CaDiCaL):
   - `cadical --lrat --no-binary Certificates/sen24.cnf Certificates/sen24.lrat`
4. Verify certificate inside Lean:
   - `lake build SocialChoiceAtlas.Sen.BaseCase24.SATSenCNF`
