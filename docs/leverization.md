# Phase1 Leverization (n=2, m=4)

This phase introduces a modular DIMACS generator while keeping the existing Sen24 baseline certificate pipeline stable.

## Baseline reproduction (UNSAT target)

```bash
python3 scripts/gen_dimacs.py \
  --n 2 --m 4 \
  --axioms asymm,un,minlib,no_cycle3,no_cycle4 \
  --out Certificates/sen24.cnf \
  --manifest Certificates/sen24.manifest.json
```

Audit baseline artifact:

```bash
python3 scripts/check_sen24_cnf.py Certificates/sen24.cnf --manifest Certificates/sen24.manifest.json --strict-duplicates --fail-on-tautology
```

Lean verification of committed LRAT:

```bash
lake build SocialChoiceAtlas.Sen.BaseCase24.SATSenCNF
```

## Lever operation example (drop MINLIB)

```bash
python3 scripts/gen_dimacs.py \
  --n 2 --m 4 \
  --axioms asymm,un,no_cycle3,no_cycle4 \
  --out /tmp/sen24_no_minlib.cnf \
  --manifest /tmp/sen24_no_minlib.manifest.json
```

This produces an auditable CNF+manifest for a relaxed axiom set (solver outcome may differ by axiom set).
You can audit it with:

```bash
python3 scripts/check_sen24_cnf.py /tmp/sen24_no_minlib.cnf --manifest /tmp/sen24_no_minlib.manifest.json
```

## Phase1 Done criteria

- Baseline `Certificates/sen24.cnf` + `Certificates/sen24.manifest.json` stay auditable.
- `scripts/gen_sen24_dimacs.py` remains backward compatible (thin wrapper).
- New modular CLI supports selectable axiom subsets.
- Auditor accepts subset manifests (`category_counts` with 0/full category counts).
- CI runs:
  - baseline CNF audit, and
  - Lean target `SocialChoiceAtlas.Sen.BaseCase24.SATSenCNF`.
