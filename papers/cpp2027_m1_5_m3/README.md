# CPP 2027 Integration Draft

This directory contains the CPP 2027 submission draft:

**Certified Impossibility Witnesses Do Not Determine Repair Reports:
A Lean-Verified Characterization of Contract-Relative Reportability**

## Source Status

- Draft version: v1
- Workspace status: canonical on `main` through PR #19
- Publication status: integrated working draft; not represented as accepted or
  submission-ready
- Format: ACM acmart SIGPLAN review / anonymous
- Main source: `main.tex`
- Bibliography: `refs.bib`
- Frozen terminology map: `../../docs/cpp2027/terminology_map_frozen.md`

## Claim Boundary

- Section 3 no-go witness: artifact-checked by deterministic regeneration,
  SHA-256 manifest binding, SAT re-solving, and repair-family
  re-verification.
- Sections 4-5 characterization: Lean-kernel checked finite-set theorem core
  under `SocialChoiceAtlas/Reportability/`.
- Section 6 concrete grouped report: bound to the independently recomputed
  finite package canonical on `main` under `../../m3/candidate_b/` through PR
  #21; artifact-level audit, not a Lean theorem, solver/proof replay, or
  semantic validation of the contract atoms.

## Build

```bash
make
```

or

```bash
latexmk -pdf -interaction=nonstopmode -halt-on-error main.tex
```

The Makefile writes the default output to `build/main.pdf`.

## G2 Checks

- PDF builds.
- Anonymous source contains no author-identifying metadata.
- Terminology follows `docs/cpp2027/terminology_map_frozen.md`.
- No superseded variable-renaming phrasing remains in the paper body.
- Candidate B claims are bound to exact manuscript text and exact evidence by
  `CLAIM_MAP_CANDIDATE_B.md`, `claim_map_candidate_b.json`, and
  `tools/cpp2027/check_candidate_b_claim_map.py` (`make claim-check`).
