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
- `atlas_schema_version` (top-level schema version for compatibility checks)
- runtime reproducibility metadata (`solver_info`, `environment_info`)
- `status_counts` over `{SAT, UNSAT, UNKNOWN}`
- per-case summaries (`status`, `solved`, selected axioms, clause counts, artifact pointers).

Safety assumption references:
- `docs/assumptions_monotone_pruning.md`
- `docs/safety_symmetry_reduction.md`

Paper-facing references:
- `docs/related_work_notes.md`
- `docs/paper_claims_map.md`
- `docs/reproducibility_appendix.md`
- `docs/evaluation_plan.md`
- `docs/sat_gallery.md`
- `docs/public_repo_security.md`

Local/private instructions:
- You can add `AGENTS.local.md` at repo root for machine-local guidance.
- It is git-ignored and must not contain repo-public content changes.

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

Storage policy:

- `Certificates/atlas/` is reserved for one fixed committed proof-carrying case (`case_11111`) to keep CI deterministic.
- Other atlas proofs should be generated under `results/...` or `/tmp`, tracked by hash (`summary.json.manifest.cnf_sha256`, `summary.json.proof.sha256`) and reproduce command (`summary.json.reproduce.command`).

Create a human-readable SAT rule sketch for one SAT case:

```bash
python3 scripts/decode_model.py --case-dir results/<YYYYMMDD>/atlas_v1/case_00000
```

`rule.md` now includes lightweight heuristic scores (dictatorship/constancy/neutrality-support variation) to flag trivial SAT solutions early.

Create atlas boundary summary markdown:

```bash
python3 scripts/summarize_atlas.py --outdir results/<YYYYMMDD>/atlas_v1
```

## Week4: symmetry classes (alts)

Compute equivalence classes using alternative relabeling (`S4`) on semantic SAT outputs:

```bash
python3 scripts/run_atlas.py \
  --outdir /tmp/atlas_w4 \
  --jobs 4 \
  --symmetry alts \
  --symmetry-check
```

Notes:
- Week4 symmetry is **alts-only** (`--symmetry alts`), not voter relabeling.
- Canonicalization uses semantic SAT outputs (`model.json` social bits), not CNF text.
- Safety guardrail: if selected axioms are not marked `SUPPORTS_SYMMETRY_ALTS=True`, run fails unless `--symmetry-unsafe-ok` is set.
- `--symmetry-check` re-solves sampled non-representatives and records `symmetry_check` stats + `checked_cases` in `atlas.json`.
- `atlas.json` includes `equiv_classes_total`, `equiv_class_histogram`, `representatives`, and per-case
  `equiv_class_id` / `representative_case` / `orbit_size`.

## Week4: monotone pruning

Use monotone closure over already-solved cases:
- if `S` is SAT, all subsets of `S` are SAT (inferred, solver skipped)
- if `U` is UNSAT, all supersets of `U` are UNSAT (inferred, solver skipped)

```bash
python3 scripts/run_atlas.py \
  --outdir /tmp/atlas_w4p \
  --prune monotone \
  --prune-check
```

Notes:
- Inferred cases are marked `solved=false` with `pruned_by` evidence in `atlas.json`.
- In prune mode, SAT/UNSAT status totals still cover all 32 cases for the 5-axiom sen24 universe.
- `prune_stats` and `oracle_stats` report solver calls avoided and inferred SAT/UNSAT counts.
- Prune evidence is validated: inferred SAT/UNSAT requires `pruned_by.derived_status/rule/witness_case_id`, with solved witness and lattice relation checks.

MUS/MCS on prune outputs:
- `scripts/mus_mcs.py` only processes `UNSAT` cases with `solved=true`.
- If all UNSAT cases are inferred (`solved=false`), rerun atlas with `--prune none` for those case masks.

## Optional incremental SAT

Week4 keeps solver mode in batch mode only. Incremental SAT via assumptions is deferred to a later phase to avoid
destabilizing the CNF schema and CI path.
