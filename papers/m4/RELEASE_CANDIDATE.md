# M4 v0.1 Release Candidate

## 1. Status

This is a local M4 v0.1 release candidate under the declared M4/Sen24 claim
boundary. It is not yet an arXiv release, Zenodo archive, public GitHub
release, or pushed tag.

`papers/m4/RELEASE_CHECKLIST.md` marks v0.1 release-candidate tagging ready
under the declared M4/Sen24 claim boundary.

## 2. Bound commit

The release-candidate binding is the commit targeted by the annotated local tag
listed below. This note is committed before the tag is created, so the exact
binding should be read from:

```text
git rev-parse papers-m4-v0.1-rc1^{}
```

The pre-note base commit was:

```text
dc8a10b161f867ac80f909350591d6a8173d89dc
```

## 3. Local tag

Planned local annotated tag:

```text
papers-m4-v0.1-rc1
```

The tag is local unless it is explicitly pushed later. This note does not
authorize pushing or public release.

## 4. Manuscript files

The M4 manuscript workspace is:

```text
papers/m4/
```

Primary manuscript files include:

- `papers/m4/main.tex`
- `papers/m4/refs.bib`
- `papers/m4/sections/*.tex`
- `papers/m4/README.md`
- `papers/m4/RELEASE_CHECKLIST.md`
- `papers/m4/reproducibility_v0_1.md`

No generated PDFs, auxiliary LaTeX files, logs, `.bbl`, `.blg`, or rendered
build outputs are intended to be committed as part of this RC.

## 5. Claim-boundary source of truth

The claim-boundary source of truth is:

```text
papers/m4/CLAIM_BOUNDARY.md
```

Manuscript, README, checklist, and release-candidate wording must not broaden
that file's claim boundary.

## 6. Evidence sources

Finite-audit evidence bindings cited by the manuscript are:

- `docs/m4_semantic_encoding_boundary.md`
- `docs/m4_scope_decision_mask_shape_phase_diagram.md`
- `docs/m4_mask_shape_collapse_law_audit_result.md`
- `docs/m4_certificate2_phase_diagram_checker_result.md`
- `docs/m4_finite_data_closure_note.md`

These are evidence-source documents. This RC does not modify them.

## 7. Lean-backed source

The Lean-backed semantic source is:

```text
SocialChoiceAtlas/Sen/RightAtomBridge.lean
```

The Lean bridge check log is:

```text
papers/m4/repro/right_atom_bridge_lean_check.log
```

The Lean bridge supports the central right-atom semantic target and limited
semantic bridge facts described in the paper. It does not prove Python/CNF
artifact correctness or semantic-to-CNF correctness.

## 8. Finite-audit replay evidence

Finite-audit replay evidence is recorded in:

- `papers/m4/repro/run_m4_finite_audit_replay.sh`
- `papers/m4/repro/m4_finite_audit_checker.log`
- `papers/m4/repro/m4_finite_audit_environment.log`
- `papers/m4/repro/m4_finite_audit_replay_summary.md`
- `papers/m4/repro/m4_v0_1_hashes.sha256`

The replay wrapper reproduces the documented 48-cell finite-audit headline
values and Certificate 2 verdict under `/tmp/sen_m4_repro/`. The checker replay
does not prove checker correctness, Python encoder correctness, CNF artifact
correctness, or Python/CNF semantic correctness.

## 9. Build command

The M4 manuscript build is run from `papers/m4/`:

```text
lualatex -interaction=nonstopmode -halt-on-error -output-directory=/tmp/sen_m4_latex_build main.tex
BIBINPUTS=. bibtex /tmp/sen_m4_latex_build/main || true
lualatex -interaction=nonstopmode -halt-on-error -output-directory=/tmp/sen_m4_latex_build main.tex
lualatex -interaction=nonstopmode -halt-on-error -output-directory=/tmp/sen_m4_latex_build main.tex
```

If TeX Live refuses direct BibTeX writes to `/tmp`, run BibTeX from the output
directory with `BIBINPUTS` pointing at `papers/m4/`, as recorded in
`papers/m4/sections/appendix_reproducibility.tex`.

## 10. Non-claims

Manual claim-boundary check result for this RC: passed.

This RC does not claim:

- Python checker correctness;
- Python encoder correctness;
- `_right_clauses` correctness;
- SAT/CNF artifact correctness;
- semantic-to-CNF correctness;
- full selector-free equivalence to Lean `MINLIB`;
- that the whole finite certificate is Lean-verified;
- a structural proof of the Mask-Shape Collapse Law;
- a new general Sen theorem;
- a family-scale lift;
- an AI governance or AI alignment solution.

## 11. Remaining future obligations

Level C semantic-to-CNF correctness remains future work. Future assurance
obligations include checker formalization or independent formal reconstruction,
Python/CNF semantic correctness, artifact-level correctness for generated CNF,
and broader family-scale work if later pursued.

These obligations are not resolved by the v0.1 RC, the Lean bridge check, or
the finite-audit replay.

## 12. Release readiness verdict

Verdict: ready for local v0.1 release-candidate tagging under the declared
M4/Sen24 claim boundary.

This verdict is local. It does not mean the tag has been pushed, published,
archived, or publicly released.
