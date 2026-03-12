# Paper Draft Workspace

This directory contains a public LaTeX skeleton for the AI/Systems-first paper framing of the Sen24 atlas pipeline.

## Build

From repository root:

```bash
python3 scripts/render_paper_assets.py --mode tiny
make -C paper pdf
```

Output PDF and auxiliary files are written under `paper/build/`.

## Reproduce figures

Regenerate the paper-facing frontier figures directly:

```bash
python3 scripts/render_paper_assets.py --mode tiny
```

This writes:

- `paper/figures/generated/frontier_matrix.png`
- `paper/figures/generated/frontier_boundary.png`
- `paper/figures/generated/frontier_hasse.dot`
- `paper/figures/generated/frontier_hasse.png`

## Paper Assets

Canonical reviewer path:

```bash
python3 scripts/render_paper_assets.py --mode tiny
```

Canonical paper-ready path:

```bash
python3 scripts/render_paper_assets.py --mode full
```

If an existing atlas already contains gallery, triangulation, baseline, and rule-card outputs, reuse it:

```bash
python3 scripts/render_paper_assets.py --mode tiny --atlas-outdir results/paper_assets/tiny_bundle/atlas
```

The artifact contract is fixed in:

```bash
docs/paper_artifact_contract.md
```

## Public repo safety

- Do not include local absolute paths, secrets, or private tokens in paper text or generated artifacts.
- Follow `docs/public_repo_security.md`.
- Keep protected baseline artifacts unchanged (`Certificates/sen24.*`, `Certificates/atlas/case_11111/**`).

## Private/local overrides

- Use `paper_private/` for private drafts, notes, or venue-specific supplements.
- `paper_private/` is git-ignored and must not be referenced by committed scripts.
