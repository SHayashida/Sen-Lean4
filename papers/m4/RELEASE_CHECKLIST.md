# M4 Preprint Release Checklist

## 1. Current status

Status: not yet ready for a v0.1 release-candidate tag without an explicit
decision on the finite-audit checker command exposure risk.

This checklist resolves the required fixes recorded in
`papers/m4/review_v0_1.md`. It does not implement optional post-v0.1
improvements, add technical results, modify Lean files, regenerate finite-audit
evidence, or broaden M4 claims.

## 2. Required fixes from v0.1 review

The review listed four required fixes before preprint release:

1. Bind the released preprint to the final release or tag commit, rather than
   leaving only the draft-start commit in the appendix.
2. Do one rendered-PDF visual pass focused on long code/path fragments and the
   two tables, because `pdftotext` showed awkward wrapping.
3. Decide whether Related Work should stay after Discussion or move earlier.
4. Preserve the qualifier "under the declared M4/Sen24 encoding" around
   finite-audit completeness language.

## 3. Resolution status

| Required fix | Status | Resolution |
| --- | --- | --- |
| Release/tag binding | resolved | Appendix A.1 now says the v0.1 release-candidate source should be cited by the release tag or repository commit containing the appendix and this checklist. The old `8e060ff` commit is retained only as historical draft-start provenance. |
| Rendered-PDF visual pass | resolved | Rendered PDF pages covering the finite-audit table, Lean bridge table, claim-boundary table, release-binding appendix, source/evidence lists, and build-command block were inspected. Presentation fixes were made for long path wrapping, escaped underscores in `\code{...}` paths, the Lean table row label, the claim-boundary table label, and shell-command spacing. |
| Related Work order | resolved | Related Work intentionally remains after Discussion and before Limitations. In this draft, the section functions as positioning after the paper has established its claim-boundary methodology; moving it earlier is not release-blocking for v0.1. |
| Declared-encoding qualifier around finite-audit completeness language | resolved | Broad "complete" wording in the abstract, introduction, background, related work, and review note was tightened to keep the finite-audit claim tied to the declared M4/Sen24 encoding or declared interface. |

No required fix from the earlier v0.1 review remains unresolved. No required
fix required new evidence, new Lean work, new scripts, regenerated artifacts,
or finite-audit evidence changes.

## 4. Claim-boundary checks

Manual claim-boundary check result: passed.

The manuscript still does not claim:

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

`papers/m4/CLAIM_BOUNDARY.md` was inspected and not modified. The release
edits stay within the existing claim boundary.

## 5. Reproducibility hardening checks

Additional release-candidate reproducibility evidence added in this pass:

- `papers/m4/reproducibility_v0_1.md`;
- `papers/m4/repro/right_atom_bridge_lean_check.log`;
- `papers/m4/repro/m4_v0_1_hashes.sha256`.

Lean bridge compilation check:

```text
lake env lean SocialChoiceAtlas/Sen/RightAtomBridge.lean
```

Result: passed with exit status `0` and no stdout/stderr.

Finite-audit checker command exposure check: documented command not found in
the inspected M4 result documents. The relevant scripts exist under
`scripts/exploration/m4/`, but no release-bound shell command was exposed in
the result docs inspected in this pass. No finite-audit checker rerun was
performed and no `papers/m4/repro/m4_finite_audit_checker.log` was created.
This remains a release-risk item for external reproducibility.

## 6. Build and citation checks

Validation commands for this pass:

```text
git diff --check
lualatex -interaction=nonstopmode -halt-on-error -output-directory=/tmp/sen_m4_latex_build main.tex
cd /tmp/sen_m4_latex_build
BIBINPUTS=/path/to/Sen-Lean4/papers/m4: bibtex main
cd /path/to/Sen-Lean4/papers/m4
lualatex -interaction=nonstopmode -halt-on-error -output-directory=/tmp/sen_m4_latex_build main.tex
lualatex -interaction=nonstopmode -halt-on-error -output-directory=/tmp/sen_m4_latex_build main.tex
```

Result: passed.

The final log scan found no unresolved citations, no undefined references, no
rerun warnings, and no serious LaTeX errors. The only warning observed was the
existing LuaLaTeX notice that `inputenc` is ignored with UTF-8 based engines.

## 7. Artifact-binding checks

The appendix names:

- the repository;
- release/tag commit binding policy for the v0.1 release candidate;
- the M4 manuscript source files;
- the Lean bridge source file;
- the finite-audit evidence documents cited by the manuscript;
- the release-candidate reproducibility evidence note;
- the Lean bridge compilation log;
- the SHA-256 evidence manifest;
- the build convention;
- the non-reproduced artifacts and future Level C obligations.

No generated PDF, auxiliary file, `.bbl`, `.blg`, log, rendered PNG, or other
build output is intended to be committed.

## 8. Remaining blockers / release risks

Finite-audit checker command exposure remains unresolved. Before tagging a
public v0.1 release candidate, either add a documented release-bound command or
wrapper for the finite-audit checker pipeline, or explicitly accept that v0.1
relies on recorded finite-data result documents rather than a one-command
external checker rerun recipe.

The M4 v0.1 preprint workspace remains within the declared M4/Sen24 claim
boundary, but this reproducibility risk should be resolved or explicitly
accepted before release-candidate tagging.

## 9. Optional post-v0.1 improvements

These items remain optional and were not implemented in this pass:

- Add a small M4 build target or documented wrapper that hides the BibTeX
  temporary-directory convention.
- Compress repeated non-claim lists if a submission venue imposes a tight page
  limit.
- Add one figure or appendix table showing the 48-cell phase diagram if the
  paper needs more visual evidence.
- Expand related work only after choosing the target venue.
