# SocialChoiceAtlas: Auditable Social Choice Evidence and Contracts

This repository began with the fixed Sen24 base case and now hosts a
multi-paper research program on auditable finite evidence, semantic obstruction
bridges, repair non-canonicity, and grouped reportability. The original Sen24
case study covers Sen's impossibility theorem for `n = 2` voters and `m = 4`
alternatives, with:

- a Lean theorem development for the sen24 semantic statement (`Theorem.lean`), and
- an independent SAT certificate pipeline (DIMACS CNF + LRAT) with committed reference artifacts checked in Lean.

For the exact M1 / Sen24 atlas claim boundary, use:
- `docs/paper_claims_map.md`
- `paper/sections/appendix_repro.tex`

These are the official source of truth for what is proved, audited, witness-validated, assumed, and re-verified.

## Research program status

For the current canonical research-program map, see
[docs/research_program_current.md](docs/research_program_current.md).

Sen24 is the audited finite base case. The current generic Sen result is a
semantic obstruction bridge: `UN + MINLIB` yields a bounded O2/O3/O4
obstruction family and hence the generic semantic impossibility theorem. The
CNF, LRAT, atlas, and repair artifacts remain base-case scoped unless a
separate bridge is established.

| Module | Current role |
|---|---|
| M1 | Finite evidence diagnosability for Sen24. |
| M1.5 | Raw repair non-canonicity under bundled/split liberalism encodings. |
| M2 | Finite semantic obstruction basis and generic Sen theorem. |
| M2.1 | Tested `(2,5)` positive track and `(3,4)` representation boundary. |
| M3 | Lean-checked abstract grouped-reportability theory with an artifact-defined Candidate B instantiation. |
| M4 | Institutional warrant, currently design-stage only. |

## Preprint submission policy (jxiv)

- Canonical repository URL: https://github.com/SHayashida/Sen-Lean4
- Preprint PDFs are **not** pushed to this repository.
- The repository tracks source and reproducibility assets (Lean/spec/scripts/docs), and each preprint submission should be tied to a specific commit hash or tag.

Recommended practice for each submission:

1. Build locally (`make -C paper pdf`).
2. Record the commit hash used for the uploaded PDF.
3. Upload only the PDF to jxiv; keep reproducibility sources in this repository.

## Multi-paper workspace policy

This repository uses one shared code/data trunk and separate in-repo manuscript workspaces.

- `paper/` is the protected M1 manuscript workspace.
- `papers/m1_5/` is the dedicated M1.5 manuscript workspace.
- Shared code, Lean artifacts, scripts, and reusable data stay on the common repository line.
- Use short-lived branches for implementation work and manuscript edits.
- Freeze submissions with tags and commit hashes rather than long-lived paper branches.

For the repository-level policy, see `docs/paper_workspace_strategy.md` and `papers/README.md`.

## Zenodo-ready layout

```text
SocialChoiceAtlas/
├── SocialChoiceAtlas/
│   ├── Core/
│   ├── Axioms/
│   └── Sen/BaseCase24/
│       ├── Spec.lean
│       ├── Theorem.lean
│       ├── SAT.lean
│       ├── SATSen.lean
│       └── SATSenCNF.lean
├── Certificates/
│   ├── README.md
│   ├── CNF_AUDIT.md
│   ├── sen24.cnf
│   ├── sen24.lrat
│   └── sen24.manifest.json
├── scripts/
│   ├── gen_sen24_dimacs.py
│   └── check_sen24_cnf.py
├── ZENODO_CLAIMS.md
├── SocialChoiceAtlas.lean
├── lakefile.lean
└── lean-toolchain
```

## Reproducibility commands

```bash
# 1) Lean proof artifacts
lake build

# 2) (optional) regenerate CNF + manifest (leverized CLI, baseline axiom set)
python3 scripts/gen_dimacs.py --n 2 --m 4 --axioms asymm,un,minlib,no_cycle3,no_cycle4

# 3) (optional) audit CNF structure against spec
python3 scripts/check_sen24_cnf.py Certificates/sen24.cnf --manifest Certificates/sen24.manifest.json

# 4) (optional) regenerate LRAT from CNF
cadical --lrat --no-binary Certificates/sen24.cnf Certificates/sen24.lrat

# 5) verify LRAT in Lean
lake build SocialChoiceAtlas.Sen.BaseCase24.SATSenCNF

# 6) Phase1/1.5 CI-equivalent local check
./scripts/ci_phase1.sh
```

## Leverized generator (Phase1)

- New modular generator: `scripts/gen_dimacs.py`
- Backward-compatible baseline wrapper: `scripts/gen_sen24_dimacs.py`
- Axiom modules live under `encoding/axioms/`
- Phase1 usage and done criteria: `docs/leverization.md`

## Atlas runner (Phase2 Week1)

- Runner: `scripts/run_atlas.py`
- Usage and artifact format: `docs/phase2_atlas.md`
- CI smoke: `./scripts/ci_phase2_smoke.sh`
- MUS/MCS enrichment: `scripts/mus_mcs.py --outdir results/<YYYYMMDD>/atlas_v1`
- Week3 committed proof-carrying Lean check: `lake build SocialChoiceAtlas.Sen.Atlas.Case11111`

## Safety assumptions

- Monotone pruning safety contract: `docs/assumptions_monotone_pruning.md`
- Symmetry reduction safety contract: `docs/safety_symmetry_reduction.md`
- Public repository security checklist: `docs/public_repo_security.md`

## Local private instructions

If you need private/local agent instructions, create `AGENTS.local.md` at repo root.
This file is git-ignored by default and can extend local workflow notes without changing the public `AGENTS.md`.

## Paper/Docs map

For paper-facing claim discipline and reproducibility narrative, use:
`docs/paper_claims_map.md` and `paper/sections/appendix_repro.tex` as the official claim boundary,
`docs/related_work_notes.md` for positioning,
and `docs/reproducibility_appendix.md` for artifact policy, `atlas_schema_version`, and solver metadata policy.
For evaluation harness metrics and figure-generation commands, see `docs/evaluation_plan.md`.
For SAT-case extraction and witness validation, see `docs/sat_gallery.md`.
For the LaTeX paper workspace and frontier figure workflow, see `paper/README.md`.
For the multi-paper repository policy and the M1.5 scaffold, see `docs/paper_workspace_strategy.md`,
`papers/README.md`, and `papers/m1_5/README.md`.

## References

- Sen, A. K. (1970). "The Impossibility of a Paretian Liberal". *Journal of Political Economy*, 78(1), 152-157.
- Geist, C. & Endriss, U. (2011). "Automated Search for Impossibility Theorems in Social Choice Theory".
- Lean 4 and mathlib4 documentation.
