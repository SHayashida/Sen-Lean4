# SocialChoiceAtlas: Sen Base Case (Lean 4 + LRAT)

This repository contains a formalized base case of Sen's impossibility theorem
for `n = 2` voters and `m = 4` alternatives, with:

- a pure Lean proof (`Theorem.lean`), and
- an independent SAT certificate pipeline (DIMACS CNF + LRAT) checked in Lean.

For the exact claim boundary ("what is guaranteed / not guaranteed"),
see `ZENODO_CLAIMS.md`.

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
- Week3 proof-carrying Lean check: `lake build SocialChoiceAtlas.Sen.Atlas.Case11111`

## Safety assumptions

- Monotone pruning safety contract: `docs/assumptions_monotone_pruning.md`
- Symmetry reduction safety contract: `docs/safety_symmetry_reduction.md`

## References

- Sen, A. K. (1970). "The Impossibility of a Paretian Liberal". *Journal of Political Economy*, 78(1), 152-157.
- Geist, C. & Endriss, U. (2011). "Automated Search for Impossibility Theorems in Social Choice Theory".
- Lean 4 and mathlib4 documentation.
