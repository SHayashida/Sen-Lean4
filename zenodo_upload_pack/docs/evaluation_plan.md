# Evaluation Plan (Phase3-Week3)

## Scope
This evaluation is sen24-fixed (`n=2`, `m=4`) and measures whether the atlas pipeline remains reproducible and explainable while adding search controls.
The evaluation focuses on monotone pruning, symmetry reduction (`--symmetry alts`), MUS/MCS enrichment, proof-carrying UNSAT metadata, and SAT triviality diagnostics.

Safety contracts for interpretation:
- `docs/assumptions_monotone_pruning.md`
- `docs/safety_symmetry_reduction.md`
- `docs/reproducibility_appendix.md`

## Metrics
Per run (`runs/<config_id>/rep_k`), collect:
- runtime: `wall_time_sec` and phase timings (`run_atlas`, `mus_mcs`, `summarize`)
- status counts: `cases_total`, `sat_count`, `unsat_count`
- solved vs inferred: `solved_true_count`, `solved_false_count`, `pruned_by_reason_counts`
- symmetry stats: `equiv_classes_total`, `orbit_size_stats` (`min/mean/max`)
- solver reproducibility: `solver_version_raw`, normalized `solver_version`, `solver_sha256`
- eval schema/repro contract: `eval_schema_version`, `reproducibility.git.commit`, `reproducibility.python.version`, `reproducibility.platform`
- seed traceability: `seed_policy` and `seeds[]` for repeated runs
- proof coverage: `unsat_proof_count`, `proof_sha256_present_rate`
- explainability: `mus_count`, `avg_mus_size`
- SAT non-triviality sample (`N=5` fixed IDs when available): dictatorship and outcome-diversity summaries

## Configurations
Default evaluation grid (`--configs` omitted):
1. `none_none` (`symmetry=none`, `prune=none`)
2. `alts_none` (`symmetry=alts`, `prune=none`)
3. `none_monotone` (`symmetry=none`, `prune=monotone`)
4. `alts_monotone` (`symmetry=alts`, `prune=monotone`)

Notes:
- `prune=monotone` is solved sequentially by design (`run_atlas.py` enforces deterministic monotone inference order).
- `symmetry=alts` is allowed only when selected axiom modules declare alts-invariance.

## Reproducibility
Canonical command to produce evaluation data (`eval.json`, `eval.csv`, per-run metrics):

```bash
python3 scripts/eval_atlas.py --outdir /tmp/atlas_eval --repeat 3 --jobs 4
```

Canonical command for runtime figure (`runtime_boxplot.png`):

```bash
python3 scripts/plot_eval.py --eval-json /tmp/atlas_eval/eval.json --figures runtime_boxplot
```

Canonical command for solved-vs-pruned figure (`solved_vs_pruned.png`):

```bash
python3 scripts/plot_eval.py --eval-json /tmp/atlas_eval/eval.json --figures solved_vs_pruned
```

Canonical command for symmetry figure (`symmetry_reduction.png`):

```bash
python3 scripts/plot_eval.py --eval-json /tmp/atlas_eval/eval.json --figures symmetry_reduction
```

## Expected outputs
- `<outdir>/runs/<config_id>/rep_<k>/atlas.json`
- `<outdir>/runs/<config_id>/rep_<k>/run_metrics.json`
- `<outdir>/eval.json`
- `<outdir>/eval.csv`
- `<outdir>/figures/runtime_boxplot.png`
- `<outdir>/figures/solved_vs_pruned.png`
- `<outdir>/figures/symmetry_reduction.png`
