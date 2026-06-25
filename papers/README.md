# Papers Workspace

This repository uses one shared code/data trunk and separate in-repo manuscript
workspaces. Paper-specific claim boundaries govern individual paper claims;
they do not broaden the repository-level dissertation scope.

Current paper workspaces on `main`:

- `paper/`: M1 finite Sen24 evidence and auditability manuscript workspace.
- `papers/m1_5/`: M1.5 raw repair non-canonicity manuscript workspace.
- `papers/m2/`: M2 finite semantic obstruction-bridge manuscript workspace.

Current publication-unit status:

| Workspace | Status |
|---|---|
| `paper/` | M1 / Sen24 finite-evidence unit. |
| `papers/m1_5/` | M1.5 workspace; publication packaging pending review with M3. |
| `papers/m2/` | M2 standalone submission unit; tagged and DOI archived, pending one-time reviewer audit. |

M2.1 and M3 paper packaging are not canonical paper workspaces on `main` in this
branch. M3 theorem-core work currently lives on the remote development branch
`origin/codex/m3-lean-reportability`; it requires a separate integration
precheck before becoming canonical.

## Non-canonical or pending workspaces

- M2.1 evidence is partly canonical through PR #9, but its manuscript workspace
  is not currently a canonical `main` workspace.
- M3 theorem and planning materials exist on a remote development branch and
  require a selective integration PR.
- M4 has no paper workspace yet.

M2.1 and M3 materials exist in non-canonical development history and require
dedicated reviewed integration before they are treated as main-branch paper
workspaces.

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
- future M1.5 or M3 tags should be chosen only when those submission units are
  actually frozen.

Hierarchy note:

Paper-specific claim boundaries override repository-level summaries. A
workspace becomes canonical only after integration into `main`; a submission
becomes frozen only through an exact tag and archival record.

TruthWeave is intentionally not the source of truth for this repository yet. If
adopted, it should be piloted on a paper-specific workflow without migrating the
existing M1 workflow.
