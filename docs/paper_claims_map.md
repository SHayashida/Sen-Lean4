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

## C3. A committed UNSAT reference can be proof-carrying and kernel-checked

- **Claim**: A committed UNSAT reference can be attached as LRAT and checked in Lean.
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

## C5. SAT gallery extraction yields auditable non-trivial SAT rule examples

- **Claim**: Relaxed SAT cases can be filtered into a deterministic, auditable gallery with explicit SAT witness validation.
- **Evidence (fields/files)**:
  - `scripts/build_sat_gallery.py` outputs: `gallery.json`, `gallery.md`
  - `scripts/validate_sat_witness.py` reports embedded under `entries[*].validator_stats`
  - schema/repro fields: `gallery_schema_version`, `atlas.atlas_sha256`, `entries[*].model_validated`
- **Canonical command**:

```bash
python3 scripts/run_atlas.py --outdir /tmp/atlas_c5 --jobs 4 --prune none && python3 scripts/build_sat_gallery.py --atlas-outdir /tmp/atlas_c5 --top-k 5 --min-k 1
```

- **Artifacts to inspect**:
  - `/tmp/atlas_c5/gallery.json`
- `/tmp/atlas_c5/gallery.md`
- `/tmp/atlas_c5/case_*/model.json`

---

## C6. Repair triangulation matches an independent optimum baseline

- **Claim**: `mcs_min_size` / `mcs_min_all` from repair enumeration matches an independent optimum baseline computed by solver-backed triangulation.
- **Evidence (fields/files)**:
  - `scripts/enumerate_repairs.py` outputs: `cases[*].mcs_all`, `cases[*].mcs_min_size`, `cases[*].mcs_min_all`
  - `scripts/triangulate_repairs.py` outputs: `repair_triangulation.json`, `repair_triangulation.md`
  - verdict fields: `cases[*].compare.{size_match,set_match}`
- **Canonical command**:

```bash
python3 scripts/run_atlas.py --outdir /tmp/atlas_c6 --jobs 4 --prune none && python3 scripts/enumerate_repairs.py --outdir /tmp/atlas_c6 && python3 scripts/triangulate_repairs.py --atlas-outdir /tmp/atlas_c6 --outdir /tmp/atlas_c6
```

- **Artifacts to inspect**:
  - `/tmp/atlas_c6/atlas.json`
  - `/tmp/atlas_c6/repair_triangulation.json`
  - `/tmp/atlas_c6/repair_triangulation.md`

---

## Scope note

All claims are intentionally scoped to sen24 and the current axiom universe. They are not claims of general `n,m` scaling.

---

## C7. Candidate B has artifact-defined grouped correctness under its declared bundled contract

- **Claim**: Candidate B is an artifact-defined M3-B instantiation under the
  declared bundled contract. Raw repair canonicity fails, while grouped
  contract-level correctness passes over the complete declared finite
  lattices.
- **Evidence (fields/files)**:
  - contract and case semantics: `m3/candidate_b/contract.json`,
    `m3/candidate_b/case_schema.json`
  - exact source binding: `m3/candidate_b/source_artifacts.json`
  - independent outputs: `m3/candidate_b/generated/`
  - guarantee ceiling: `m3/candidate_b/CLAIM_BOUNDARY.md`
- **Canonical command**:

```bash
./scripts/ci_m3_candidate_b.sh
```

- **Artifacts to inspect**:
  - `m3/candidate_b/generated/audit_result.json`
  - `m3/candidate_b/generated/residual_faithfulness.json`
  - `m3/candidate_b/generated/group_soundness_full.json`
  - `m3/candidate_b/generated/grouped_correctness_pointwise.json`
  - `m3/candidate_b/MANIFEST.sha256`

This claim is artifact-defined. It does not establish Candidate B in Lean,
semantic validity of the contract atoms, encoder or solver correctness,
normative optimality of grouping, or family-scale transfer.
