# Papers Workspace

This repository uses one shared code/data trunk and separate in-repo manuscript workspaces.

Current paper workspaces:

- `paper/`: M1 manuscript workspace kept as the default and protected path.
- `papers/m1_5/`: M1.5 manuscript workspace for the next paper.

Operating rules:

- Use `main` as the integration branch for shared code, Lean artifacts, scripts, docs, and reusable data.
- Use short-lived Git branches for implementation and writing tasks.
- Treat each submission as a tagged commit snapshot rather than a long-lived paper branch.
- Keep paper-specific claim boundaries, reproducibility notes, and generated assets inside each paper workspace.
- Keep shared code and data in common repository locations unless a paper requires a frozen copy for reproducibility.

Suggested tag names:

- `m1-submission-v1`
- `m15-draft-v1`

TruthWeave is intentionally not the source of truth for this repository yet. If adopted, it should be piloted on `papers/m1_5/` first without migrating the existing M1 workflow.
