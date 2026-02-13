# Paper Claims Map (Claim → Evidence → Canonical Command → Artifacts)

This document fixes a one-to-one mapping from claim to concrete evidence and a single canonical reproduction command.

---

## C1. Atlas generation yields a small-scope SAT/UNSAT frontier

- **Claim**: For sen24 (`n=2,m=4`), axiom-lever enumeration yields a reproducible SAT/UNSAT frontier.
- **Evidence (fields/files)**:
  - `scripts/run_atlas.py` output: `atlas.json`, `atlas_summary.md`
  - reproducibility fields: `atlas_schema_version`, `solver_info.solver_version_raw`, `solver_info.solver_version`
- **Canonical command**:

```bash
python3 scripts/run_atlas.py --outdir /tmp/atlas_c1 --jobs 4 --prune none && python3 scripts/summarize_atlas.py --outdir /tmp/atlas_c1
```

- **Artifacts to inspect**:
  - `/tmp/atlas_c1/atlas.json`
  - `/tmp/atlas_c1/atlas_summary.md`
  - `/tmp/atlas_c1/case_*/summary.json`

---

## C2. UNSAT boundary is explainable via MUS/MCS

- **Claim**: UNSAT boundary cases are explainable via one MUS and one small MCS candidate.
- **Evidence (fields/files)**:
  - `scripts/mus_mcs.py` output: per-case `mus.json`, `mcs.json`
  - `atlas.json` embeddings: `cases[*].mus`, `cases[*].mcs`, top-level `mus_mcs`
- **Canonical command**:

```bash
python3 scripts/run_atlas.py --outdir /tmp/atlas_c2 --jobs 4 --prune none && python3 scripts/mus_mcs.py --outdir /tmp/atlas_c2
```

- **Artifacts to inspect**:
  - `/tmp/atlas_c2/case_*/mus.json`
  - `/tmp/atlas_c2/case_*/mcs.json`
  - `/tmp/atlas_c2/atlas.json`

---

## C3. UNSAT can be proof-carrying and kernel-checked

- **Claim**: UNSAT evidence can be attached as LRAT and checked in Lean.
- **Evidence (fields/files)**:
  - committed reference: `Certificates/atlas/case_11111/{sen24.cnf,proof.lrat}`
  - Lean target: `SocialChoiceAtlas.Sen.Atlas.Case11111`
  - dynamic run field: `summary.json.proof.sha256` (for regenerated case)
- **Canonical command**:

```bash
python3 scripts/run_atlas.py --outdir /tmp/atlas_c3 --jobs 1 --case-masks 31 --emit-proof unsat-only && lake build SocialChoiceAtlas.Sen.Atlas.Case11111
```

- **Artifacts to inspect**:
  - `Certificates/atlas/case_11111/*`
  - `/tmp/atlas_c3/case_11111/summary.json` (`proof.sha256`)

---

## C4. Symmetry reduction + monotone pruning are safe under explicit conditions

- **Claim**: Symmetry/pruning usage is guarded by explicit assumptions and runtime validators.
- **Evidence (fields/files)**:
  - assumptions docs:
    - `docs/assumptions_monotone_pruning.md`
    - `docs/safety_symmetry_reduction.md`
  - guardrails in outputs:
    - `symmetry_check.{checked_k,mismatches,checked_cases}`
    - top-level `checked_cases`
    - inferred-case `pruned_by.{derived_status,rule,witness_case_id}`
- **Canonical command**:

```bash
python3 scripts/run_atlas.py --outdir /tmp/atlas_c4 --jobs 1 --prune monotone --prune-check --symmetry alts --symmetry-check
```

- **Artifacts to inspect**:
  - `/tmp/atlas_c4/atlas.json` (`symmetry_check`, `checked_cases`, `prune_stats`, `oracle_stats`, `cases[*].pruned_by`)

---

## Scope note

All claims are intentionally scoped to sen24 and the current axiom universe. They are not claims of general `n,m` scaling.
