# M4 v0.1 Preprint Review

## 1. Overall verdict

Conditional go for an internal v0.1 preprint review, after minor release-binding
and presentation cleanup. The draft is coherent, readable, and unusually clear
about what it does not prove. It should not yet be treated as a polished
submission manuscript, mainly because the release binding, visual PDF polish,
and section-order decision still need final attention.

Pre-edit `git diff --check` passed. I also built the PDF and reviewed extracted
PDF text directly, not only the TeX source.

## 2. Main claim as understood by a reviewer

M4 is a claim-boundary audit for finite social-choice artifacts. Under a
declared Sen24 encoding, it presents a complete finite audit, a partial
Lean-backed semantic target, and explicit future correctness obligations.

The paper's strongest safe claim is not that Sen's theorem is newly proved, not
that the Python/CNF artifacts are semantically verified, and not that the whole
finite certificate is Lean-verified. The safe claim is that the finite repair
and reporting statements are audited inside a declared interface, while the
semantic and implementation bridges are separated into named layers.

## 3. Strong points

- The abstract and introduction make the motivating problem clear before the
  technical vocabulary takes over.
- The paper consistently marks "under the declared encoding" as the operative
  scope of the finite audit.
- Section 4 gives concrete finite-audit substance: 48 cells, 18 `ALL_UNSAT`
  cells, 30 `ALL_SAT` cells, 816 repair objects, 46 repair orbits, 46 cell
  report fibers, and 33 shape-blind fibers.
- Section 5 is clear that the Lean bridge is a semantic target, not a
  Python/CNF correctness proof.
- The limitations section is direct and useful. Its first sentence correctly
  prevents a reader from turning the paper into an end-to-end verification
  claim.
- The appendix names the source files, Lean bridge file, finite-audit source
  documents, and build convention. That is enough for v0.1 artifact binding.

## 4. Major risks

1. The phrase "complete finite audit" is safe only while it stays attached to
   "under the declared M4/Sen24 encoding." Any later shortening to "complete
   audit" would overstate the result.
2. Related Work appears after Discussion and before Limitations. This order is
   defensible for v0.1, but some reviewers may expect Related Work before the
   discussion or immediately before limitations.
3. The repeated non-claim lists in Sections 1, 3, 5, 6, 8, and 9 protect the
   claim boundary, but they also make the draft feel defensive in places.
4. The PDF text extraction shows rough wrapping for long code/path fragments
   and table entries. This is not a claim problem, but it is a presentation
   risk for a public preprint.
5. The appendix records the draft start commit rather than a final release or
   tag. That is correct for the current draft, but it must be updated or
   supplemented before an archived release.

## 5. Overclaim audit

No direct overclaim was found in the inspected source or extracted PDF text.
The dangerous terms occur, but mostly in scoped or negative contexts.

- `complete`: used as "complete finite audit" or "audit completely"; safe when
  tied to the declared Sen24 interface.
- `proof`, `theorem`, `Lean`: safe. The draft distinguishes Lean-backed
  semantic facts from Python/CNF and artifact-level correctness.
- `certificate`, `certified`, `verified`: mostly safe, though the paper should
  avoid any unqualified future use of "verified." Section 7 explicitly warns
  against hiding layers behind that word.
- `semantic`, `correctness`, `correct`: safe. These terms are usually used to
  name future Level C obligations or to describe the limited Lean semantic
  target.
- `collapse`, `law`: safe. The draft says the Mask-Shape Collapse Law is not
  structurally proved here.
- `general`, `family`: safe. The draft repeatedly says no new general Sen
  theorem or family-scale lift is claimed.
- `AI governance`, `alignment`: safe. These are framed as downstream relevance
  and explicit non-claims.

The draft does not claim Python encoder correctness, `_right_clauses`
correctness, SAT/CNF artifact correctness, semantic-to-CNF correctness, full
selector-free equivalence to Lean `MINLIB`, a Lean-verified whole certificate,
a structural proof of the Mask-Shape Collapse Law, a new general Sen theorem,
a family-scale lift, or an AI governance/alignment solution.

Plain-language entry check: the first two abstract sentences and the first
introduction paragraph pass the banned-term check in substance. They introduce
decision-rule impossibility, evidence, and licensed reporting before Lean,
CNF, certificate layers, or mask/shape terminology appear.

## 6. Section-by-section notes

- Abstract: Clear and scoped. It states the contribution and major non-claim in
  one paragraph.
- Introduction: Strong problem-first opening. The non-claim paragraph is long
  but useful for claim discipline.
- Background: Good lineage from M1 through M3. It avoids re-claiming M2 or M3
  results as M4 contributions.
- Declared Encoding: Clear trust-boundary section. The distinction between an
  interface declaration and a semantic equivalence proof is well stated.
- Finite Audit: Technically substantive enough for v0.1. The compact table is
  essential and should remain. A direct pointer to the appendix evidence
  binding was added during this review.
- Lean Bridge: Clear distinction among semantic target, orientation
  invariance, sufficient `MINLIB` direction, and future Python/CNF work.
- Claim Boundaries: Useful synthesis, though it partly repeats Sections 3 and
  5. Keep it unless the paper later needs compression.
- Discussion: Works as a methodological synthesis. It should not drift into
  general automated governance claims.
- Related Work: Adequate for v0.1. It positions SAT-based computational social
  choice, certified SAT/formal verification, diagnosis/repair, and abstraction
  or reportability.
- Limitations: Strong. The explicit future Level C list is reviewer-facing and
  should remain.
- Appendix: The source and build binding is clear. The release/tag binding
  should be refreshed before public archival release.

## 7. Citation and related-work notes

The v0.1 bibliography is sufficient for the current claim. It covers Sen,
SAT-based social choice, certified SAT/proof artifacts, Lean/formal methods,
diagnosis, MaxSAT, constraint hierarchies, and mechanized social choice.

No must-cite omission blocks v0.1. Before a venue submission, the related-work
section should be checked for more recent certified-SAT and computational
social-choice references, but that is not necessary for this review commit.

## 8. Reproducibility and artifact-binding notes

The appendix correctly states that it does not introduce a new solver run, new
generated artifact, or new proof of encoding correctness. It names the M4
source files, the claim-boundary file, the Lean bridge file, the finite-audit
documents, and the LaTeX build convention.

The build sequence required a BibTeX working-directory adjustment in practice:
running `bibtex main` from `/tmp/sen_m4_latex_build` with `BIBINPUTS` pointing
to `papers/m4` resolved the bibliography cleanly. The generic command in the
appendix is acceptable for v0.1 because it avoids committing local absolute
paths, but a future release should consider a small make target or wrapper.

No PDF, aux, bbl, blg, log, or other build output should be committed.

## 9. Required fixes before preprint release

1. Bind the released preprint to the final release or tag commit, rather than
   leaving only the draft-start commit in the appendix.
2. Do one rendered-PDF visual pass focused on long code/path fragments and the
   two tables, because `pdftotext` shows awkward wrapping.
3. Decide whether Related Work should stay after Discussion or move earlier.
   The current order is acceptable for v0.1, but the decision should be
   intentional before public release.
4. Preserve the qualifier "under the declared M4/Sen24 encoding" around every
   use of "complete finite audit."

## 10. Optional improvements after v0.1

- Add a small M4 build target or documented wrapper that hides the BibTeX
  temporary-directory convention.
- Add artifact hashes or a release manifest once the paper is archived.
- Compress repeated non-claim lists if a submission venue imposes a tight page
  limit.
- Add one figure or appendix table showing the 48-cell phase diagram if the
  paper needs more visual evidence.
- Expand related work only after choosing the target venue.
