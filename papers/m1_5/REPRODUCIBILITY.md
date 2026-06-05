# M1.5 Reproducibility Note

This note records the repository policy for reproducing the M1.5 manuscript.

## Workspace policy

- Manuscript root: `papers/m1_5/`
- Default shared integration branch: `main`
- Paper submissions should be frozen with tags rather than long-lived paper branches.

## Artifact policy

- Shared code, Lean files, scripts, and reusable data remain in their common repository locations.
- M1.5-generated paper assets must write to `papers/m1_5/figures/generated/` and `papers/m1_5/tables/generated/`.
- Result directories backing M1.5 claims should be isolated from M1-facing bundles, for example under `results/paper_assets/m1_5/` or a paper-specific experiment directory.

## Minimum reproduction record

Each M1.5 draft or submission should record:

- the commit hash,
- the submission tag, if any,
- the commands used to generate figures/tables,
- the result directories or manifest hashes backing each paper claim.

## Current scaffold commands

```bash
python3 scripts/render_paper_assets.py --paper-id m1_5 --mode tiny
make -C papers/m1_5 pdf
```

## Scope boundary

This file applies only to M1.5. It does not replace `docs/reproducibility_appendix.md` or the M1 paper-specific appendix under `paper/sections/appendix_repro.tex`.
