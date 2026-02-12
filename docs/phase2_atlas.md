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
    mus.json        # Week2 enrichment (for UNSAT)
    mcs.json        # Week2 enrichment (for UNSAT)
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

## Week2: MUS/MCS enrichment

After `run_atlas.py`, enrich UNSAT cases with one MUS and one small MCS candidate:

```bash
python3 scripts/mus_mcs.py --outdir results/<YYYYMMDD>/atlas_v1
```

This updates `atlas.json` in-place and writes per-case `mus.json` / `mcs.json`.

## Week3: proof-carrying + explainable outputs

Generate atlas cases with UNSAT proof emission:

```bash
python3 scripts/run_atlas.py \
  --outdir results/<YYYYMMDD>/atlas_v1 \
  --jobs 4 \
  --emit-proof unsat-only
```

Verify the committed proof-carrying atlas case in Lean:

```bash
lake build SocialChoiceAtlas.Sen.Atlas.Case11111
```

Create a human-readable SAT rule sketch for one SAT case:

```bash
python3 scripts/decode_model.py --case-dir results/<YYYYMMDD>/atlas_v1/case_00000
```

Create atlas boundary summary markdown:

```bash
python3 scripts/summarize_atlas.py --outdir results/<YYYYMMDD>/atlas_v1
```
