# Figures Directory

- Place generated M2 figures under `papers/m2/figures/generated/`.
- Keep this workspace independent from `paper/figures/generated/` and
  `papers/m1_5/figures/generated/`.
- As of the initial scaffold, M2 has no auto-generated figures; the positive
  flagship is text + Lean reference, and Negative #1 is a text-driven scope
  wall. If a figure becomes necessary (e.g. a diagram of the Proof-vs-Witness
  boundary), wire it through `scripts/render_paper_assets.py --paper-id m2`.
