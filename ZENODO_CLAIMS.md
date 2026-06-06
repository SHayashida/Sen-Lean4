# Public Claim Boundary for Release Artifacts

The official public source of truth for claims is:
- `docs/paper_claims_map.md`
- `paper/sections/appendix_repro.tex`

This note is only a short release-facing summary and does not override those files.

## What the release artifacts support

1. Sen24 semantic theorem in Lean
   - `SocialChoiceAtlas/Sen/BaseCase24/Theorem.lean` proves the fixed sen24 semantic statement for the base case (`n=2`, `m=4`).
2. Committed proof-carrying UNSAT reference artifact
   - `SocialChoiceAtlas/Sen/BaseCase24/SATSenCNF.lean` checks the committed pair `Certificates/sen24.cnf` and `Certificates/sen24.lrat` in the Lean kernel.
3. Audited CNF artifact contract
   - `scripts/check_sen24_cnf.py` audits variable numbering, clause-family counts, and manifest consistency for the committed sen24 artifact family.

## What the release artifacts do not claim

1. General `n,m` scalability or multi-theorem completeness
   - The scope is the fixed sen24 case study only.
2. Whole-atlas proof-carrying guarantees
   - Proof-carrying applies only to committed UNSAT reference artifacts, not to the atlas as a whole.
3. End-to-end mechanized semantic encoding correctness
   - The semantics-to-CNF boundary remains an audited contract plus explicit assumptions.
4. Generic performance or solver-superiority claims
   - No general runtime, memory, or optimization-superiority claims are made.

## Minimal reproduction path

1. `lake build`
2. `python3 scripts/gen_sen24_dimacs.py`
3. `python3 scripts/check_sen24_cnf.py Certificates/sen24.cnf --manifest Certificates/sen24.manifest.json`
4. `cadical --lrat --no-binary Certificates/sen24.cnf Certificates/sen24.lrat`
5. `lake build SocialChoiceAtlas.Sen.BaseCase24.SATSenCNF`

## Artifact traceability

- Lean semantic theorem:
  - `SocialChoiceAtlas/Sen/BaseCase24/Theorem.lean`
- Committed LRAT replay in Lean:
  - `SocialChoiceAtlas/Sen/BaseCase24/SATSenCNF.lean`
  - `Certificates/sen24.cnf`
  - `Certificates/sen24.lrat`
- CNF audit contract:
  - `scripts/gen_sen24_dimacs.py`
  - `scripts/check_sen24_cnf.py`
  - `Certificates/sen24.manifest.json`
  - `Certificates/CNF_AUDIT.md`
