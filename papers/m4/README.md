# M4 Preprint Workspace

This directory contains the working draft of the M4 preprint:

```text
Auditable Claim Boundaries for Finite Social-Choice Artifacts: A Sen24 Case Study
```

## Status

This workspace is in v0.1 release-candidate hardening. Current readiness and
release risks are recorded in `papers/m4/RELEASE_CHECKLIST.md`, with
reproducibility evidence summarized in `papers/m4/reproducibility_v0_1.md`.
It remains a preprint workspace rather than a venue-submission manuscript.

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
does not yet define a paper-specific build target. A minimal bibliography and
reproducibility appendix are included for review.

Current lightweight build sequence from `papers/m4/`:

```text
lualatex -interaction=nonstopmode -halt-on-error -output-directory=/tmp/sen_m4_latex_build main.tex
cd /tmp/sen_m4_latex_build
BIBINPUTS=/path/to/Sen-Lean4/papers/m4: bibtex main
cd /path/to/Sen-Lean4/papers/m4
lualatex -interaction=nonstopmode -halt-on-error -output-directory=/tmp/sen_m4_latex_build main.tex
lualatex -interaction=nonstopmode -halt-on-error -output-directory=/tmp/sen_m4_latex_build main.tex
```

Add a `Makefile` and archival record only when the preprint workspace moves
beyond v0.1 release-candidate review.

Do not commit generated PDFs or auxiliary LaTeX outputs unless a later
repository policy or paper-release decision explicitly requires them.
