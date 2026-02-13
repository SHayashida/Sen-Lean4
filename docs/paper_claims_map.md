# Paper Claims Map (Claim → Evidence → Reproduce → Artifacts)

This file maps intended paper-level claims to concrete repository evidence and runnable commands.

---

## C1. Atlas generation over axiom levers yields a SAT/UNSAT frontier in small scope

- **Claim**: For sen24 (`n=2,m=4`), enumerating axiom subsets yields a reproducible SAT/UNSAT frontier.
- **Evidence**:
  - `scripts/run_atlas.py`
  - `atlas.json`
  - `atlas_summary.md` (`scripts/summarize_atlas.py`)
- **Reproduce**:

```bash
python3 scripts/run_atlas.py --outdir /tmp/atlas_c1 --jobs 4 --prune none
python3 scripts/summarize_atlas.py --outdir /tmp/atlas_c1
```

- **Artifacts**:
  - `/tmp/atlas_c1/atlas.json`
  - `/tmp/atlas_c1/atlas_summary.md`
  - per-case `summary.json`, `sen24.cnf`, `sen24.manifest.json`
  - top-level metadata: `atlas_schema_version`, `solver_info`, `environment_info`, `symmetry_*`, `prune_*`

---

## C2. UNSAT boundary is explainable via MUS/MCS

- **Claim**: UNSAT boundary cases can be explained by one deletion-based MUS and one small MCS candidate.
- **Evidence**:
  - `scripts/mus_mcs.py`
  - per-case `mus.json`, `mcs.json`
  - embedded `mus`/`mcs` blocks in `atlas.json`
- **Reproduce**:

```bash
python3 scripts/run_atlas.py --outdir /tmp/atlas_c2 --jobs 4 --prune none
python3 scripts/mus_mcs.py --outdir /tmp/atlas_c2
```

- **Artifacts**:
  - `/tmp/atlas_c2/case_*/mus.json`
  - `/tmp/atlas_c2/case_*/mcs.json`
  - `/tmp/atlas_c2/atlas.json` with `mus_mcs` + per-case `mus`/`mcs`

---

## C3. UNSAT results can be proof-carrying and kernel-checked

- **Claim**: UNSAT can be backed by LRAT and checked by Lean kernel.
- **Evidence**:
  - committed proof-carrying artifact:
    - `Certificates/atlas/case_11111/sen24.cnf`
    - `Certificates/atlas/case_11111/proof.lrat`
  - Lean target:
    - `SocialChoiceAtlas.Sen.Atlas.Case11111`
- **Reproduce**:

```bash
# committed artifact check
lake build SocialChoiceAtlas.Sen.Atlas.Case11111

# optional dynamic re-generation for one atlas case
python3 scripts/run_atlas.py --outdir /tmp/atlas_c3 --jobs 1 --case-masks 31 --emit-proof unsat-only
```

- **Artifacts**:
  - committed: `Certificates/atlas/case_11111/*`
  - regenerated (optional): `/tmp/atlas_c3/case_11111/proof.lrat` + `summary.json.proof`

---

## C4. Symmetry reduction + monotone pruning are safe under explicit conditions

- **Claim**: Symmetry/pruning are applied under explicit assumptions and guarded by runtime validation.
- **Evidence**:
  - assumptions docs:
    - `docs/assumptions_monotone_pruning.md`
    - `docs/safety_symmetry_reduction.md`
  - guards in `scripts/run_atlas.py`:
    - symmetry capability checks (`SUPPORTS_SYMMETRY_ALTS`)
    - `--symmetry-check`
    - pruning witness validator (`pruned_by` integrity + lattice relation)
- **Reproduce**:

```bash
python3 scripts/run_atlas.py --outdir /tmp/atlas_c4_sym --jobs 1 --case-masks 0,1,31 --symmetry alts --symmetry-check
python3 scripts/run_atlas.py --outdir /tmp/atlas_c4_prune --jobs 1 --prune monotone --prune-check
python3 scripts/summarize_atlas.py --outdir /tmp/atlas_c4_prune
```

- **Artifacts**:
  - `/tmp/atlas_c4_sym/atlas.json` with `symmetry_check`, `checked_cases`
  - `/tmp/atlas_c4_prune/atlas.json` with `pruned_by`, `prune_stats`, `oracle_stats`

---

## Scope note

All claims above are scoped to sen24 (`n=2,m=4`) and the current axiom universe. They are not claims of general scaling.
