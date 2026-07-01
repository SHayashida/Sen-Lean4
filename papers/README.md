# Papers Workspace

This repository uses one shared code/data trunk and separate in-repo manuscript
workspaces. Paper-specific claim boundaries govern individual paper claims;
they do not broaden the repository-level dissertation scope.

Current paper workspaces on `main`:

- `paper/`: M1 finite Sen24 evidence and auditability manuscript workspace.
- `papers/m1_5/`: M1.5 raw repair non-canonicity manuscript workspace.
- `papers/m2/`: M2 finite semantic obstruction-bridge manuscript workspace.
- `papers/m4/`: M4 auditable claim-boundary preprint workspace (Sen24 case study).

Current publication-unit status:

| Workspace | Publication-unit status |
|---|---|
| `paper/` | M1 / Sen24 finite-evidence unit. |
| `papers/m1_5/` | M1.5 workspace; possible integrated publication with M3 remains undecided. |
| `papers/m2/` | M2 standalone unit; archived and reviewer-audited `CONDITIONAL GO`; major revision required before submission. |
| `papers/m4/` | M4 claim-boundary preprint unit; v0.1 draft reproducibility hardening and finite-audit replay evidence are recorded. |

## M3 theorem core and paper status

The M3 abstract Lean theorem core is canonical in the shared code trunk under
`SocialChoiceAtlas/Reportability/`. This canonical code status does not imply a
canonical M3 manuscript workspace.

There is no canonical `papers/m3/` workspace on `main`. Current M3 prose
documents need freshness revision before any manuscript packaging decision.
Candidate B evidence is not canonical; it still requires a curated evidence
package plus validator, or an immutable release binding. M1.5+M3 publication
packaging remains under decision.

Any future M3 submission needs its own workspace, claim boundary, exact tag, and
archival record.

## Non-canonical or pending workspaces

- M2.1 evidence is partly canonical through PR #9, but its manuscript workspace
  is not currently a canonical `main` workspace.
- Candidate B evidence packaging is pending and must not be treated as canonical
  paper evidence yet.
- M4 now has a `papers/m4/` v0.1 draft preprint workspace. The Lean
  right-atom bridge check and finite-audit replay wrapper are recorded; RC
  readiness is governed by `papers/m4/RELEASE_CHECKLIST.md`.
- Stale M3 planning documents in development history are not a canonical paper
  workspace.

Operating rules:

- Use `main` as the integration branch for shared code, Lean artifacts, scripts,
  docs, and reusable data.
- Use short-lived Git branches for implementation and writing tasks.
- Treat each submission as a tagged commit snapshot rather than a long-lived
  paper branch.
- Keep paper-specific claim boundaries, reproducibility notes, and generated
  assets inside each paper workspace.
- Keep shared code and data in common repository locations unless a paper
  requires a frozen copy for reproducibility.
- Do not silently broaden dissertation scope through paper workspace edits; use
  `docs/doctoral_scope_lock.md` for scope changes.

Suggested tag names:

- `m1-submission-v1`
- `papers-m2-v2-obstruction-bridge`
- future M1.5, M3, or M4 tags should be chosen only when those submission units
  are actually frozen.

Hierarchy note:

Paper-specific claim boundaries override repository-level summaries. A
workspace becomes canonical only after integration into `main`; a submission
becomes frozen only through an exact tag and archival record.

TruthWeave is intentionally not the source of truth for this repository yet. If
adopted, it should be piloted on a paper-specific workflow without migrating the
existing M1 workflow.
