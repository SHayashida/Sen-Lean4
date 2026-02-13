# SAT Gallery (Phase4-Week1)

## Motivation

The atlas pipeline already identifies UNSAT boundaries (with MUS/MCS and proof-carrying UNSAT checks).
The SAT Gallery adds the complementary case-study view: extract concrete SAT rules that appear after relaxing axiom levers, then validate each selected SAT witness against CNF.

This is a minimal, deterministic, reproducible extraction layer for paper figures and tables.

## Non-trivial heuristics

The gallery uses lightweight heuristics to avoid obviously trivial SAT rules.
These are **heuristics**, not theorem-level guarantees.

Default thresholds:
- `distinct_social_outcomes >= 2`
- `dictatorship_score_max <= 0.95`
- `constant_function_rate <= 0.999999`

Selection is deterministic:
1. `distinct_social_outcomes` (descending)
2. `dictatorship_score_max` (ascending)
3. `neutrality_violation_count` (ascending, if available)
4. `case_id` (lexicographic)

If too few cases pass the heuristic filter, selection backfills from remaining SAT candidates up to `min_k`.

## SAT witness validation

`python3 scripts/validate_sat_witness.py` verifies each selected SAT witness against DIMACS CNF without trusting solver output strings.

- Parses CNF directly.
- Reads model assignment from `model.json`.
- Checks all clauses are satisfied.
- Reports clause/assignment statistics.

`build_sat_gallery.py` records `model_validated` and validator stats for each selected entry.

## Reproduction commands

Generate an atlas run (example):

```bash
python3 scripts/run_atlas.py --outdir /tmp/atlas_phase4 --jobs 4 --prune none
```

Generate rule summaries for SAT cases (optional pre-step; gallery can call this automatically when needed):

```bash
python3 scripts/decode_model.py --case-dir /tmp/atlas_phase4/case_00000
```

Build SAT gallery artifacts:

```bash
python3 scripts/build_sat_gallery.py --atlas-outdir /tmp/atlas_phase4 --top-k 5 --min-k 1
```

Validate one SAT witness manually:

```bash
python3 scripts/validate_sat_witness.py --cnf /tmp/atlas_phase4/case_00000/sen24.cnf --model /tmp/atlas_phase4/case_00000/model.json
```

## Artifact policy

- Do not commit mass generated gallery artifacts.
- Generate gallery outputs under `results/...` or `/tmp`.
- Keep baseline protection unchanged:
  - `Certificates/sen24.cnf`
  - `Certificates/sen24.manifest.json`
  - `Certificates/atlas/case_11111/*`
- Gallery outputs must use sanitized, relative paths only (no local absolute paths).
