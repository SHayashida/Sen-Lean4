# Reviewer Quickstart

This guide provides a reviewer-oriented reproduction path for claims `C1`–`C6` with a tiny run and a full run.

## 10-minute path (tiny evidence bundle)

Run a compact bundle that still includes SAT/UNSAT atlas outputs, repairs, triangulation, gallery, and paper-facing assets:

```bash
python3 scripts/build_evidence_bundle.py --mode tiny --outdir /tmp/sen24_bundle_tiny --solver cadical --jobs 1 --symmetry none --prune none
```

Expected key outputs:

- `/tmp/sen24_bundle_tiny/bundle.json`
- `/tmp/sen24_bundle_tiny/atlas/atlas.json`
- `/tmp/sen24_bundle_tiny/atlas/gallery.json`
- `/tmp/sen24_bundle_tiny/atlas/repair_triangulation.json`
- `/tmp/sen24_bundle_tiny/paper/figures/generated/frontier_matrix.png`
- `/tmp/sen24_bundle_tiny/paper/figures/generated/frontier_hasse.png`
- `/tmp/sen24_bundle_tiny/paper/tables/generated/repairs_table.tex`
- `/tmp/sen24_bundle_tiny/paper/tables/generated/gallery_table.tex`
- `/tmp/sen24_bundle_tiny/paper/tables/generated/triangulation_table.tex`

## 30-minute path (full 32-case atlas bundle)

Run the full bundle over all 32 sen24 axiom subsets:

```bash
python3 scripts/build_evidence_bundle.py --mode full --outdir /tmp/sen24_bundle_full --solver cadical --jobs 4 --symmetry none --prune none
```

Optional standalone table regeneration:

```bash
python3 scripts/maxsat_baseline.py --atlas-outdir /tmp/sen24_bundle_full/atlas --case-id case_11111
python3 scripts/gen_paper_tables.py --atlas-outdir /tmp/sen24_bundle_full/atlas --outdir /tmp/sen24_bundle_full/paper/tables/generated
```

Expected differences vs tiny mode:

- full `atlas.cases_total = 32`
- repair/triangulation outputs cover all solved UNSAT cases in full scope
- gallery ranking is computed over the full SAT candidate pool

## Claims mapping (C1-C6)

This mapping is aligned with `docs/paper_claims_map.md`.

- `C1`: `atlas/atlas.json`, `atlas/atlas_summary.md`
- `C2`: `atlas/case_*/mus.json`, `atlas/case_*/mcs.json`, `atlas.json` embedded fields
- `C3`: committed proof-carrying reference `Certificates/atlas/case_11111/**` and Lean target `SocialChoiceAtlas.Sen.Atlas.Case11111`
- `C4`: atlas fields `symmetry_check`, `checked_cases`, `prune_stats`, `cases[*].pruned_by`
- `C5`: `atlas/gallery.json`, `atlas/gallery.md`, per-case `rule_card.md/.tex`, witness validation stats
- `C6`: `atlas/repair_triangulation.json`, `atlas/repair_triangulation.md`, comparison fields `size_match`/`set_match`
  and `atlas/maxsat_baseline.json` (tiny MAXSAT-style sanity baseline for minimum repair size)

## What to verify

Use this checklist when reviewing outputs:

- schema versions exist and are valid:
  - `bundle.bundle_schema_version >= 1`
  - `atlas.atlas_schema_version >= 1`
  - `gallery.gallery_schema_version >= 1`
- `bundle.artifacts.files[*].sha256` is present for produced files
- SAT gallery entries satisfy:
  - `entries[*].model_validated == true`
  - `entries[*].non_trivial == true`
- repair minimality artifacts exist:
  - `cases[*].mcs_all`, `mcs_min_size`, `mcs_min_all` (for solved UNSAT cases)
- triangulation comparison passes:
  - `repair_triangulation.json` has `size_match == true` and `set_match == true` for listed cases
- tiny MAXSAT baseline is present:
  - `maxsat_baseline.json` has `schema_version >= 1`, `min_repair_size`, and `one_repair_set`
- path safety:
  - no `/Users/` or `C:\` fragments in bundle `JSON/MD/TEX/CSV/DOT` files

## Re-running baseline checks

Run repository smoke checks before or after bundle reproduction:

```bash
./scripts/ci_phase1.sh
./scripts/ci_phase2_smoke.sh
```
