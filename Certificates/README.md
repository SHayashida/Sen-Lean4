# SAT/LRAT Certificate Verification

This directory will contain LRAT proof certificates for SAT-based
verification of social choice impossibility theorems.

## Overview

The approach uses SAT solvers to verify finite instances of impossibility
theorems, then imports the proof certificates into Lean for kernel-level
verification.

## Workflow

### 1. Problem Encoding

Encode the theorem as a CNF (Conjunctive Normal Form) formula:

```
Variables:
- p_i_x_y: voter i prefers x to y in profile p
- s_p_x_y: society strictly prefers x to y under profile p

Clauses:
- Unanimity constraints
- Decisiveness constraints  
- Acyclicity constraints (negated for UNSAT proof)
```

### 2. SAT Solving with LRAT Generation

Use a SAT solver that produces LRAT proofs:

```bash
# Using CaDiCaL
cadical sen_basecase24.cnf --lrat sen_basecase24.lrat

# Using Kissat
kissat sen_basecase24.cnf --lrat=sen_basecase24.lrat
```

### 3. Certificate Trimming (Optional)

LRAT certificates can be large. Use `lrat-trim` to reduce size:

```bash
lrat-trim sen_basecase24.lrat sen_basecase24_trimmed.lrat
```

### 4. Lean Verification

Replace `bv_decide` with `bv_check`:

```lean
-- In SocialChoiceAtlas/Sen/BaseCase24/SAT.lean
theorem sen_sat_verified : encoded_impossibility := by
  bv_check "Certificates/sen_basecase24.lrat"
```

## File Structure

```
Certificates/
├── README.md                    # This file
├── sen_basecase24.cnf          # CNF encoding (future)
├── sen_basecase24.lrat         # LRAT certificate (future)
└── scripts/
    └── encode_sen.py           # Encoding script (future)
```

## Advantages of Certificate-Based Proofs

1. **Reproducibility**: Same certificate verifies on any machine
2. **Speed**: Verification is O(n) in certificate size, much faster than solving
3. **Trust**: Lean's kernel checks the proof, not the solver
4. **Extensibility**: Easy to add new base cases (different n, m)

## Base Cases to Generate

| Voters (n) | Alternatives (m) | Status |
|------------|------------------|--------|
| 2          | 4                | TODO   |
| 2          | 5                | TODO   |
| 3          | 4                | TODO   |
| 3          | 5                | TODO   |

## Tools Required

- [CaDiCaL](https://github.com/arminbiere/cadical) - SAT solver with LRAT
- [DRAT-trim](https://github.com/marijnheule/drat-trim) - Certificate trimmer
- Python 3.x - For CNF encoding scripts

## References

- Heule, M. (2017). "The DRAT format and DRAT-trim checker"
- Lean 4 `bv_decide` documentation
- Geist, C. & Endriss, U. (2011). "Automated Search for Impossibility Theorems"
