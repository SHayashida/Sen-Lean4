# Paper Draft Workspace

This directory contains a public LaTeX skeleton for the AI/Systems-first paper framing of the Sen24 atlas pipeline.

## Build

From repository root:

```bash
make -C paper pdf
```

Output PDF and auxiliary files are written under `paper/build/`.

## Reproduce figures

1. Generate atlas data (example):

```bash
python3 scripts/run_atlas.py --outdir /tmp/atlas_phase4_paper --jobs 4 --prune none
```

2. Generate frontier figures:

```bash
python3 scripts/plot_frontier.py --atlas-outdir /tmp/atlas_phase4_paper --outdir paper/figures/generated --format png
```

3. (Optional) Generate evaluation figures:

```bash
python3 scripts/eval_atlas.py --outdir /tmp/atlas_eval_paper --repeat 3 --jobs 4
python3 scripts/plot_eval.py --eval-json /tmp/atlas_eval_paper/eval.json --outdir paper/figures/generated
```

## Reproduce evidence bundle

```bash
python3 scripts/build_evidence_bundle.py --mode tiny --outdir /tmp/sen24_bundle_tiny --solver cadical --jobs 1
python3 scripts/gen_paper_tables.py --atlas-outdir /tmp/sen24_bundle_tiny/atlas --outdir /tmp/sen24_bundle_tiny/paper/tables/generated
```

## Public repo safety

- Do not include local absolute paths, secrets, or private tokens in paper text or generated artifacts.
- Follow `docs/public_repo_security.md`.
- Keep protected baseline artifacts unchanged (`Certificates/sen24.*`, `Certificates/atlas/case_11111/**`).

## Private/local overrides

- Use `paper_private/` for private drafts, notes, or venue-specific supplements.
- `paper_private/` is git-ignored and must not be referenced by committed scripts.
