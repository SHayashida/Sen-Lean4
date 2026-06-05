# Multi-Paper Repository Strategy

This note records the repository policy for running M1 and M1.5 in one codebase.

## Branch model

- `main` is the integration branch for shared code, Lean artifacts, scripts, docs, and reusable data.
- Use short-lived branches for code changes, experiments, manuscript edits, and paper asset updates.
- Do not use a long-lived paper branch as the primary separator between M1 and M1.5.

Reason:

- long-lived paper branches accumulate merge debt,
- shared code/data fixes become harder to propagate,
- submission reproducibility becomes branch-history dependent instead of commit/tag based.

## Manuscript workspaces

- `paper/` remains the M1 manuscript workspace.
- `papers/m1_5/` is the dedicated M1.5 manuscript workspace.

Each paper workspace should own:

- manuscript sources,
- paper-specific generated figures/tables,
- a claim boundary note,
- a reproducibility note.

## Shared code and data

- Keep core scripts, Lean files, and reusable data in shared repository locations.
- Bind paper claims to explicit result directories or artifact hashes rather than to implicit local state.
- If a paper requires incompatible experiment logic, isolate it by config, result directory, or paper-facing entrypoint instead of copying core code.

## Submission policy

- Freeze submissions with tags, for example `m1-submission-v1` or `m15-draft-v1`.
- Record the commit hash and the asset-generation commands used for each submission.
- Treat the tag as the paper snapshot; do not rely on a long-lived branch name as the archival reference.

## TruthWeave adoption policy

TruthWeave is not the immediate source of truth for this repository.

Recommended order:

1. keep the existing M1 workflow stable,
2. separate M1.5 into its own in-repo workspace,
3. if needed, pilot TruthWeave on M1.5 only,
4. migrate additional papers only after the pilot proves useful.
