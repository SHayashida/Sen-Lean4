# M2 Reproducibility Note

This note records the repository policy for reproducing the M2 manuscript
(Bridge Theorems / Transfer Contract).

## Workspace Policy

- Manuscript root: `papers/m2/`
- Construction branch: the current M2 bridge branch used for the manuscript
  snapshot
- Paper submissions should be frozen with tags rather than long-lived paper
  branches.

## Artifact Policy

- The generic semantic obstruction bridge lives at
  `SocialChoiceAtlas/Sen/ObstructionBridge.lean` and is kernel-checked by
  default `lake build` via the root import in `SocialChoiceAtlas.lean`.
- The legacy compatibility theorem lives at
  `SocialChoiceAtlas/Sen/Lifting/ImpossibilityLift.lean`.
- The scope wall is text-first and lives at `docs/m2_scope_wall.md`. It is not
  a Lean theorem; it is a guarantee-boundary statement.
- M2-generated paper assets, if any, must write to
  `papers/m2/figures/generated/` and `papers/m2/tables/generated/`. M2 has no
  new solver-generated artifacts.

## Minimum Reproduction Record

Each M2 draft or submission should record:

- the commit hash on the M2 bridge branch;
- the submission tag, if any;
- the Zenodo DOI, once the tagged release has been archived;
- the command used to typecheck the obstruction bridge;
- the command used to typecheck the legacy compatibility theorem;
- the M2 smoke-gate outcome (`./scripts/ci_m2_smoke.sh`);
- the root build outcome (`lake build`);
- the manuscript build outcome (`make -C papers/m2 pdf`);
- the decision-record state (`docs/gates/m2/aim_signoff.md`).

## Current Scaffold Commands

```bash
# Kernel-check the generic obstruction bridge.
lake env lean SocialChoiceAtlas/Sen/ObstructionBridge.lean

# Kernel-check the legacy compatibility theorem.
lake env lean SocialChoiceAtlas/Sen/Lifting/ImpossibilityLift.lean

# Run the M2 smoke-gate.
./scripts/ci_m2_smoke.sh

# Run the root build.
lake build

# Build the manuscript.
make -C papers/m2 pdf
```

## Artifact Binding

| Claim | Binding |
|---|---|
| Witness extraction / classification | `SocialChoiceAtlas/Sen/ObstructionBasis.lean` |
| Generic profile construction | `SocialChoiceAtlas/Sen/ObstructionProfiles.lean` |
| Shape soundness and exact cardinalities | `SocialChoiceAtlas/Sen/ObstructionSoundness.lean` |
| Generic bridge and impossibility theorem | `SocialChoiceAtlas/Sen/ObstructionBridge.lean` |
| Legacy compatibility corollary | `SocialChoiceAtlas/Sen/Lifting/ImpossibilityLift.lean` |
| Root build integration | `SocialChoiceAtlas.lean` |
| M2 smoke integration | `scripts/ci_m2_smoke.sh` |
| Witness/Audit scope wall | `docs/m2_scope_wall.md` |

## Scope Boundary

This file applies only to M2. It does not replace
`docs/reproducibility_appendix.md`, the M1 paper-specific appendix under
`paper/sections/appendix_repro.tex`, or the M1.5 reproducibility note under
`papers/m1_5/REPRODUCIBILITY.md`.

For the release procedure and DOI insertion pattern, see `papers/m2/ZENODO.md`.

## What Is Not Reproduced Here

- Candidate-B / Negative #2 (representation non-canonicity at family scale) is
  ratified-deferred to **M2.1**. Its reproduction record will be authored
  alongside that milestone, not here.
- No new solver runs and no new CNF artifacts are part of M2.
- The CNF Witness/Audit layer remains scoped to the existing Sen24 baseline.
- No repair/MCS transfer, atlas transfer, or LRAT family-level certificate is
  reproduced here.
