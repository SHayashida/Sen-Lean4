# Reproducibility Appendix (Phase3)

## Artifact policy

- Baseline artifacts are fixed and protected:
  - `Certificates/sen24.cnf`
  - `Certificates/sen24.manifest.json`
- Proof-carrying atlas artifacts under `Certificates/atlas/` are limited to one committed reference case:
  - `Certificates/atlas/case_11111/*`
- Other atlas cases are regenerated under `results/...` or `/tmp/...`, then tracked by hashes and reproduce metadata:
  - `summary.json.manifest.cnf_sha256`
  - `summary.json.proof.sha256` (if UNSAT proof exists)
  - `summary.json.reproduce.command`

## `atlas_schema_version` policy

- `atlas_schema_version` is a top-level integer in `atlas.json`.
- **Bump rule**: increment only on breaking schema changes (field removal/rename or semantics-breaking restructure).
- CI currently guarantees:
  - field exists,
  - integer type,
  - lower bound (`>= 1`).
- CI does **not** guarantee full backward compatibility across arbitrary versions.
- Older atlases are treated as unsupported unless an explicit migration/conversion path is added.

## Solver metadata policy

Each atlas stores reproducibility metadata:

- `solver_info.solver_name`
- `solver_info.solver_path`
- `solver_info.solver_version_raw` (as reported by solver probe)
- `solver_info.solver_version` (normalized if recognizable, else `"unknown"`)
- `solver_info.solver_sha256` (best-effort binary hash)

Fallback behavior:

- If probing fails, values may be `"unknown"`; this is explicit and auditable.

## Determinism notes

- Monotone pruning uses sequential evaluation (even if `--jobs > 1` is passed, it is ignored with warning) to keep inference order deterministic.
- Symmetry class representative choice is deterministic:
  - `representative_case` is the lexicographically smallest case ID in class.
- Symmetry validation (`--symmetry-check`) stores `checked_cases` to make sampled checks auditable.

## Minimal reproduction checklist

```bash
# Phase1 baseline integrity
./scripts/ci_phase1.sh

# Phase2 smoke (atlas generation + checks + Lean case check)
./scripts/ci_phase2_smoke.sh

# Direct Lean check for committed proof-carrying case
lake build SocialChoiceAtlas.Sen.Atlas.Case11111
```

## Limitations

- Reproducibility is strongest for fixed sen24 scope and committed baseline artifacts.
- Cross-platform solver packaging differences can change `solver_version_raw`; this is why both raw and normalized forms are stored.
