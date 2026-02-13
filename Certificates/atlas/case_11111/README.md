# Atlas Case `case_11111` (sen24)

This directory stores a committed proof-carrying UNSAT artifact for the atlas case where all five axioms are enabled:

- `asymm`
- `un`
- `minlib`
- `no_cycle3`
- `no_cycle4`

Files:

- `sen24.cnf`: DIMACS encoding for this case
- `sen24.manifest.json`: schema/count metadata
- `proof.lrat`: LRAT UNSAT certificate

Lean verification target:

```bash
lake build SocialChoiceAtlas.Sen.Atlas.Case11111
```

