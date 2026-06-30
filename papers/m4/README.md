# M4 Preprint Workspace

This directory contains the working draft of the M4 preprint:

```text
Auditable Claim Boundaries for Finite Social-Choice Artifacts: A Sen24 Case Study
```

## Status

This workspace is not submission-ready. `main.tex` and the files under
`sections/` form the current preprint draft, with the claim-boundary discipline
kept explicit while the manuscript is revised.

## Source Of Truth

`papers/m4/CLAIM_BOUNDARY.md` is the source of truth for M4 paper claims.
Manuscript prose in this directory must not broaden those claims.

In particular, the paper must not claim:

- Python encoder correctness;
- generated CNF artifact correctness;
- semantic-to-CNF correctness;
- full selector-free encoding equivalence to Lean `MINLIB`;
- a new general Sen theorem;
- family-scale CNF, LRAT, atlas, or repair lifts.

## Build Policy

The LaTeX files are written to be syntactically reasonable, but this workspace
does not yet define a paper-specific build target. Add a `Makefile`,
reproducibility note, bibliography, and archival record only when the preprint
workspace moves beyond draft status.

Do not commit generated PDFs or auxiliary LaTeX outputs unless a later
repository policy or paper-release decision explicitly requires them.
