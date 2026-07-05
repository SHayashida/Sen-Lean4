# CPP 2027 Integration Draft

This directory contains the CPP 2027 submission draft:

**Certified Impossibility Witnesses Do Not Determine Repair Reports:
A Lean-Verified Characterization of Contract-Relative Reportability**

## Source Status

- Draft version: v1
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
- Section 6 concrete grouped report: artifact-level audit, not a Lean theorem.

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
