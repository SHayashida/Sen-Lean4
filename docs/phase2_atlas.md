# Phase2 Week1: Atlas Runner (sen24 fixed)

`scripts/run_atlas.py` enumerates axiom subsets for the fixed base case (`n=2`, `m=4`) and writes per-case artifacts plus `atlas.json`.

## Quick start

Dry-run (generate CNF + manifest only):

```bash
python3 scripts/run_atlas.py --dry-run
```

Run with solver (default `cadical`):

```bash
python3 scripts/run_atlas.py \
  --solver cadical \
  --jobs 4 \
  --prune none
```

Run a subset of masks (useful for smoke/debug):

```bash
python3 scripts/run_atlas.py \
  --dry-run \
  --case-masks 0,1,31 \
  --outdir /tmp/atlas_smoke
```

## Output layout

```
results/<YYYYMMDD>/atlas_v1/
  atlas.json
  case_<bits>/
    sen24.cnf
    sen24.manifest.json
    solver.log
    summary.json
    model.json      # SAT and model parsed
    proof.lrat      # UNSAT and proof emitted/supported
```

`case_id` uses a stable bitmask over `axiom_universe` order:
- bit `i` corresponds to `axiom_universe[i]`
- `1` means the axiom is enabled
- e.g. with universe `asymm,un,minlib,no_cycle3,no_cycle4`, `case_11111` is baseline.

## atlas.json

`atlas.json` contains:
- run metadata (`solver`, `prune`, `jobs`, `dry_run`, universe order)
- `status_counts` over `{SAT, UNSAT, UNKNOWN, PRUNED}`
- per-case summaries (`status`, selected axioms, clause counts, artifact pointers).

