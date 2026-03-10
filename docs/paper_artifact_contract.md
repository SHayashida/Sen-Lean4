# Paper Artifact Contract

This document is the single source of truth for paper-facing artifacts used by the sen24 manuscript.
It is intentionally aligned with the current official claims map in `docs/paper_claims_map.md`.
It does not broaden any claim.

## Canonical commands

Reviewer-scale path:

```bash
python3 scripts/render_paper_assets.py --mode tiny
```

Paper-ready path:

```bash
python3 scripts/render_paper_assets.py --mode full
```

Reuse an existing atlas that already contains gallery, triangulation, baseline, and rule-card outputs:

```bash
python3 scripts/render_paper_assets.py --mode tiny --atlas-outdir results/paper_assets/tiny_bundle/atlas
```

## CI status labels

- `existence`: `scripts/ci_phase2_smoke.sh` checks that the artifact is actually produced.
- `help`: CI checks only that the producer script exposes `--help`.
- `none`: the artifact is documented but not directly checked in CI.

## Artifact table

| Artifact | Supporting claim(s) | Producing script | Canonical command | Output path | CI status | Required for paper-ready build? |
| --- | --- | --- | --- | --- | --- | --- |
| `frontier_matrix.png` | `C1` | `scripts/plot_frontier.py` | `python3 scripts/render_paper_assets.py --mode full` | `paper/figures/generated/frontier_matrix.png` | `existence` | Yes |
| `frontier_boundary.png` | `C1`, `C2` | `scripts/plot_frontier.py` | `python3 scripts/render_paper_assets.py --mode full` | `paper/figures/generated/frontier_boundary.png` | `existence` | Yes |
| `frontier_hasse.dot` | `C1`, `C4` | `scripts/plot_hasse_frontier.py` | `python3 scripts/render_paper_assets.py --mode full` | `paper/figures/generated/frontier_hasse.dot` | `existence` | Yes |
| `frontier_hasse.png` | `C1`, `C4` | `scripts/plot_hasse_frontier.py` | `python3 scripts/render_paper_assets.py --mode full` | `paper/figures/generated/frontier_hasse.png` | `existence` | Yes |
| `repairs_table.tex` | `C6` | `scripts/gen_paper_tables.py` | `python3 scripts/render_paper_assets.py --mode full` | `paper/tables/generated/repairs_table.tex` | `existence` | Yes |
| `gallery_table.tex` | `C5` | `scripts/gen_paper_tables.py` | `python3 scripts/render_paper_assets.py --mode full` | `paper/tables/generated/gallery_table.tex` | `existence` | Yes |
| `triangulation_table.tex` | `C6` | `scripts/gen_paper_tables.py` | `python3 scripts/render_paper_assets.py --mode full` | `paper/tables/generated/triangulation_table.tex` | `existence` | Yes |
| `selected_rule_card.tex` | `C5` | `scripts/build_sat_gallery.py` via `scripts/render_paper_assets.py` | `python3 scripts/render_paper_assets.py --mode full` | `paper/tables/generated/selected_rule_card.tex` | `existence` | Yes |
| `bundle.json` | reviewer path for `C1`-`C6` | `scripts/build_evidence_bundle.py` | `python3 scripts/render_paper_assets.py --mode tiny` | `results/paper_assets/tiny_bundle/bundle.json` | `existence` | No |

## Contract notes

- `scripts/render_paper_assets.py` is the preferred interface for paper-facing assets. It uses existing generator scripts and standardizes outputs under:
  - `paper/figures/generated/`
  - `paper/tables/generated/`
- The narrower official `C2` claim remains `one MUS + one small MCS candidate`. The paper uses `frontier_boundary.png` plus the per-case `mus.json` / `mcs.json` artifacts for that claim.
- The stronger repair tables belong to `C6`, not `C2`.
- `frontier_hasse.png` is best-effort rendering from `frontier_hasse.dot`; if Graphviz is unavailable, the DOT file remains the primary guaranteed artifact.
