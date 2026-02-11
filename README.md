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

# 2) (optional) regenerate CNF + manifest
python3 scripts/gen_sen24_dimacs.py

# 3) (optional) audit CNF structure against spec
python3 scripts/check_sen24_cnf.py Certificates/sen24.cnf --manifest Certificates/sen24.manifest.json

# 4) (optional) regenerate LRAT from CNF
cadical --lrat --no-binary Certificates/sen24.cnf Certificates/sen24.lrat

# 5) verify LRAT in Lean
lake build SocialChoiceAtlas.Sen.BaseCase24.SATSenCNF
```

## References

- Sen, A. K. (1970). "The Impossibility of a Paretian Liberal". *Journal of Political Economy*, 78(1), 152-157.
- Geist, C. & Endriss, U. (2011). "Automated Search for Impossibility Theorems in Social Choice Theory".
- Lean 4 and mathlib4 documentation.
