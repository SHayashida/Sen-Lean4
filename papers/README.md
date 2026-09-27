# Papers Workspace

This repository uses one shared code/data trunk and separate in-repo manuscript
workspaces. Paper-specific claim boundaries govern individual paper claims;
they do not broaden the potential doctoral-scope candidate recorded for program
planning.

Current paper workspaces on `main`:

- `paper/`: M1 finite Sen24 evidence and auditability manuscript workspace.
- `papers/m1_5/`: M1.5 raw repair non-canonicity manuscript workspace.
- `papers/m2/`: M2 finite semantic obstruction-bridge manuscript workspace.
- `papers/m1_5_m3/`: venue-neutral integrated M1.5+M3 research-draft
  workspace; the former CPP 2027 submission plan is discontinued.
- `papers/m4/`: M4 auditable claim-boundary preprint workspace (Sen24 case study).

Current publication-unit status:

| Workspace or evidence | Artifact class | Publication-unit status |
|---|---|---|
| `paper/` | Public/preprint manuscript workspace | M1 / Sen24 finite-evidence unit. |
| `papers/m1_5/` | Canonical manuscript workspace | M1.5 standalone source and witness claim boundary; also an input to the integrated M1.5+M3 draft. |
| `papers/m2/` | Public/preprint and archived canonical workspace | M2 standalone unit; reviewer-audited `CONDITIONAL GO`; major revision required before submission. |
| `papers/m1_5_m3/` | Canonical venue-neutral integrated research draft | Former CPP 2027 v1 workspace through PR #19; submission plan discontinued on 2026-08-19, with no current venue target. |
| `tools/check_cm_witness.py` plus the M1.5 anonymous-supplement workflow | Artifact-only evidence binding | Canonical M1.5 C1-C5 checker and hashes. |
| `m3/candidate_b/` | Canonical artifact-defined application evidence on `main` | Full finite Candidate B M3-B package, independent validator, manifest, fault tests, and separate anonymous builder; immutable release/redistribution review pending; not a Lean theorem or semantic validation. |
| `papers/m4/` | Repository-local tagged RC workspace | Sen24 claim-boundary RC; not a GitHub Release or the immediate publication track. The institutional-warrant M4 theorem remains future work. |
| M2.1 | Deferred manuscript | Evidence is partly canonical through PR #9; no canonical manuscript workspace is claimed. |

## M3 theorem core and paper status

The M3 abstract Lean theorem core is canonical in the shared code trunk under
`SocialChoiceAtlas/Reportability/`. This canonical code status does not imply a
canonical M3 manuscript workspace.

There is no separate canonical `papers/m3/` workspace on `main`.
`papers/m1_5_m3/` is instead the canonical integrated M1.5+M3
working-draft workspace. Its abstract characterization uses the M3 Lean core;
its concrete witness remains artifact-checked.

PR #18 made the M1.5 C1-C5 witness binding canonical through a deterministic
checker, exact hashes, and the anonymous-supplement builder. The distinct
`m3/candidate_b/` package now freezes the full finite M3-B application evidence
and recomputes its contract-relative obligations. Its default curated rebuild
is self-contained in a clean clone; historical mode retains the exact source
provenance audit. Neither status makes
Candidate B a Lean theorem, validates its contract atoms semantically, or
verifies the encoder or solver.

Any separate future M3 submission needs its own workspace, claim boundary,
exact tag, and archival record.

## Non-canonical or pending workspaces

- M2.1 evidence is partly canonical through PR #9, but its manuscript workspace
  is not currently a canonical `main` workspace.
- Candidate B has no immutable tag or public Release; do not confuse release
  status with the canonical repository package or the narrower M1.5 binding.
- M4 now has a `papers/m4/` v0.1 draft preprint workspace. The Lean
  right-atom bridge check and finite-audit replay wrapper are recorded. This is
  a repository-local release-candidate workspace, not a public release; Level C
  semantic-to-CNF correctness, Python/CNF correctness, and checker
  formalization remain future work. RC readiness is governed by
  `papers/m4/RELEASE_CHECKLIST.md`.
- Stale M3 planning documents in development history are not a canonical paper
  workspace.
- The Dafny formal-model-repair repository is a workflow pilot, not a manuscript
  workspace or general M3 validation.
- The XAI companion is deferred or parallel. No public manuscript or artifact
  status is inferred by this repository.

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
- Do not silently broaden the potential doctoral-scope candidate through paper
  workspace edits; use `docs/doctoral_scope_lock.md` for scope changes.

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
