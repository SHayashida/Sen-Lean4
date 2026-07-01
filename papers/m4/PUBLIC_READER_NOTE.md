# M4 Public Reader Note

## What this workspace is

`papers/m4/` is a local v0.1 release-candidate preprint workspace for
Auditable Claim Boundaries for Finite Social-Choice Artifacts: A Sen24 Case
Study. The paper studies how to state and audit finite-artifact claims under a
declared M4/Sen24 encoding without silently upgrading those claims into broader
semantic or family-scale theorems.

This workspace is intended for claim-boundary review before public release. It
is not an arXiv, Zenodo, jxiv, GitHub Release, or pushed-tag public release.
Readers should treat it as a source snapshot for discussion: useful for
checking whether the claim boundary, replay commands, and non-claim language
are coherent, but not as an archival version or submission package.

## What is currently bound

The local release-candidate binding is documented in
`papers/m4/RELEASE_CANDIDATE.md`. The checklist in
`papers/m4/RELEASE_CHECKLIST.md` records the v0.1 RC readiness decision under
the declared M4/Sen24 claim boundary. Those files should be read together with
`papers/m4/CLAIM_BOUNDARY.md`, which is the source of truth for what the M4
paper may and may not claim.

The manuscript source is `papers/m4/main.tex`, with section files under
`papers/m4/sections/` and bibliography data in `papers/m4/refs.bib`.

## What to read first

Start with:

- `papers/m4/main.tex` for the manuscript source;
- `papers/m4/CLAIM_BOUNDARY.md` for allowed claims and non-claims;
- `papers/m4/RELEASE_CANDIDATE.md` for the local RC binding;
- `papers/m4/RELEASE_CHECKLIST.md` for the readiness checklist;
- `papers/m4/reproducibility_v0_1.md` for reproducibility evidence and limits.

These files are public-facing summaries. They do not replace the paper-specific
claim boundary.

The repository also contains earlier M1-M3 work and internal review notes. They
provide background for the broader program, but they should not be used to
infer stronger M4 claims than the files listed here allow.

## Reproducibility evidence

The RC workspace records two main reproducibility checks. The finite-audit
replay wrapper is `papers/m4/repro/run_m4_finite_audit_replay.sh`, with the
summary in `papers/m4/repro/m4_finite_audit_replay_summary.md`. The Lean
right-atom bridge compilation check is recorded in
`papers/m4/repro/right_atom_bridge_lean_check.log`.

These checks support the local RC claim-boundary audit under the declared
M4/Sen24 encoding. They do not prove the Python checker correct, do not prove
generated CNF artifacts correct, and do not establish semantic-to-CNF
correctness. The replay evidence is therefore best read as reproducibility
support for the stated finite-audit result, not as a formal proof of every
software or artifact boundary in the pipeline.

## What is not claimed

M4 v0.1 does not claim Python encoder correctness, `_right_clauses`
correctness, SAT/CNF artifact correctness, semantic-to-CNF correctness, full
selector-free equivalence to Lean `MINLIB`, or that the whole finite
certificate is Lean-verified. It also does not claim a structural proof of the
Mask-Shape Collapse Law, a new general Sen theorem, a family-scale lift, or an
AI governance or AI alignment solution.

Level C semantic-to-CNF correctness, checker formalization or independent
formal reconstruction, Python/CNF semantic correctness, and artifact-level
correctness for generated CNF remain future assurance obligations.
