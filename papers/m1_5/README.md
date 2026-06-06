# M1.5 Paper Workspace

This directory is the dedicated manuscript workspace for the second paper (M1.5).

## Build

From repository root:

```bash
python3 scripts/render_paper_assets.py --paper-id m1_5 --mode tiny
make -C papers/m1_5 pdf
```

Output PDF and auxiliary files are written under `papers/m1_5/build/`.

## Reproduce paper-facing assets

Reviewer-scale asset generation:

```bash
python3 scripts/render_paper_assets.py --paper-id m1_5 --mode tiny
```

Paper-ready asset generation:

```bash
python3 scripts/render_paper_assets.py --paper-id m1_5 --mode full
```

Reuse an existing atlas when available:

```bash
python3 scripts/render_paper_assets.py --paper-id m1_5 --mode tiny --atlas-outdir results/paper_assets/m1_5/tiny_bundle/atlas
```

## Paper-specific contract

- Claim boundary: `papers/m1_5/CLAIM_BOUNDARY.md`
- Reproducibility note: `papers/m1_5/REPRODUCIBILITY.md`

These files must remain specific to M1.5 and must not silently expand the claim scope of `paper/`.

## Shared code/data policy

- Shared scripts, Lean code, and common data remain in the repository root layout.
- M1.5 should point to explicit result directories and artifact hashes for any paper claim.
- If M1.5 requires incompatible experiment logic, isolate it through separate configs, result directories, or paper-facing entrypoints rather than copying core code.

## Public repo safety

- Do not include local absolute paths, secrets, or private tokens in manuscript text or generated assets.
- Follow `docs/public_repo_security.md`.
- Keep protected baseline artifacts unchanged (`Certificates/sen24.*`, `Certificates/atlas/case_11111/**`).

## TruthWeave status

TruthWeave is not required for this workspace. If adopted later, use it as an audit layer for M1.5 without changing the existing M1 manuscript workflow.
