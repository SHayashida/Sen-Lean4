# M2 Reproducibility Note

This note records the repository policy for reproducing the M2 manuscript
(Bridge Theorems / Transfer Contract).

## Workspace policy

- Manuscript root: `papers/m2/`
- Construction branch: `codex/m2-bridge`
- Paper submissions should be frozen with tags rather than long-lived paper
  branches.

## Artifact policy

- The positive flagship theorem lives in `SocialChoiceAtlas/Sen/Lifting/` and
  is kernel-checked by default `lake build` via the root import in
  `SocialChoiceAtlas.lean` (Decision 3 in `docs/gates/m2/aim_signoff.md`).
- The scope wall (Negative #1) is text-first and lives at
  `docs/m2_scope_wall.md`. It is not (yet) a Lean theorem; it is a
  guarantee-boundary statement.
- M2-generated paper assets, if any, must write to
  `papers/m2/figures/generated/` and `papers/m2/tables/generated/`. As of the
  initial scaffold, M2 has no auto-generated figures; the manuscript is
  text-driven and refers to a kernel-checked Lean module and a decision-record
  document.

## Minimum reproduction record

Each M2 draft or submission should record:

- the commit hash on `codex/m2-bridge`;
- the submission tag, if any;
- the build command used to typecheck the lift module;
- the M2 smoke-gate outcome (`./scripts/ci_m2_smoke.sh`);
- the decision-record state (`docs/gates/m2/aim_signoff.md`).

## Current scaffold commands

```bash
# Kernel-check the M2 positive flagship via narrow target.
lake build SocialChoiceAtlas.Sen.Lifting.ImpossibilityLift

# Run the M2 smoke-gate (invariants documented in scripts/ci_m2_smoke.sh).
./scripts/ci_m2_smoke.sh

# Build the manuscript.
make -C papers/m2 pdf
```

## Scope boundary

This file applies only to M2. It does not replace
`docs/reproducibility_appendix.md`, the M1 paper-specific appendix under
`paper/sections/appendix_repro.tex`, or the M1.5 reproducibility note under
`papers/m1_5/REPRODUCIBILITY.md`.

## What is NOT reproduced here

- Candidate-B / Negative #2 (representation non-canonicity at family scale) is
  ratified-deferred to **M2.1**. Its reproduction record will be authored
  alongside that milestone, not here.
- No new solver runs and no new CNF artifacts are part of M2. The CNF Witness/
  Audit layer remains scoped to the existing sen24 baseline.
