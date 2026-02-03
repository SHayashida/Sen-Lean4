# SAT/LRAT Certificate Verification

This directory contains LRAT proof certificates for SAT-based verification of social choice impossibility theorems.

## Overview

The SocialChoiceAtlas project uses SAT solvers to verify finite instances of impossibility theorems, particularly Sen's "Impossibility of a Paretian Liberal" theorem. The proof certificates are imported into Lean 4 for kernel-level verification, ensuring the highest level of mathematical rigor.

## Current Implementation

### Sen's Theorem Base Case (n=2, m=4)

We have implemented a verified base case for Sen's theorem with:
- **n = 2** voters
- **m = 4** alternatives

The implementation uses Lean 4's `Std.Tactic.BVDecide` framework for SAT-based verification.

## Workflow

### Internal Workflow with BVDecide

The recommended approach for this repository uses Lean's built-in SAT solver integration:

1. **Build with `bv_decide`** (solver runs during compilation):
   ```bash
   lake build SocialChoiceAtlas.Sen.BaseCase24.SATSenGenerated
   ```

2. **Generate LRAT certificate** (one-time):
   - Edit [SocialChoiceAtlas/Sen/BaseCase24/SATSenGenerated.lean](../SocialChoiceAtlas/Sen/BaseCase24/SATSenGenerated.lean) and replace `bv_decide` with `bv_decide?` in the `sen24_unsat` theorem
   - Rebuild to generate the certificate:
     ```bash
     lake build SocialChoiceAtlas.Sen.BaseCase24.SATSenGenerated
     ```

3. **Cache the certificate**:
   - The generated `.lrat` file will be placed next to `SATSenGenerated.lean`
   - Switch the proof to `bv_check "sen24_unsat.lrat"` for fast cached verification
   - Commit the `.lrat` file to the repository

### Problem Encoding

The Sen theorem is encoded as a CNF (Conjunctive Normal Form) formula representing the impossibility of simultaneously satisfying:
- **Pareto Optimality**: If all voters prefer x to y, society prefers x to y
- **Minimal Liberalism**: Each voter is decisive on at least one pair of alternatives
- **Rational Social Preference**: Social preferences form a transitive and complete ordering

#### Variables

- `p_i_x_y`: voter i prefers alternative x to alternative y in profile p
- `s_p_x_y`: society strictly prefers x to y under profile p

#### Constraints

- Unanimity constraints (Pareto)
- Minimal decisiveness constraints (Liberalism)
- Acyclicity constraints (Rationality)
- Negation of satisfiability (proving UNSAT establishes the impossibility)

### External SAT Solving with LRAT (Alternative Approach)

For larger instances, you can use external SAT solvers that produce LRAT proofs:

```bash
# Using CaDiCaL
cadical problem.cnf --lrat proof.lrat

# Using Kissat  
kissat problem.cnf --lrat=proof.lrat
```

#### Certificate Trimming (Optional)

LRAT certificates can be large. Use `lrat-trim` to reduce size:

```bash
lrat-trim proof.lrat proof_trimmed.lrat
```

#### Lean Verification

Replace `bv_decide` with `bv_check` to use the cached certificate:

```lean
-- In SocialChoiceAtlas/Sen/BaseCase24/SAT.lean
theorem sen_sat_verified : encoded_impossibility := by
  bv_check "Certificates/sen_basecase24.lrat"
```

## Repository Structure

```
Certificates/
├── README.md                    # This file
└── (future) LRAT certificates for additional base cases

SocialChoiceAtlas/
├── Core/
│   ├── Basics.lean              # Fundamental definitions
│   ├── Ranking.lean             # Preference rankings
│   └── Profile.lean             # Voter profiles
├── Axioms/
│   ├── Pareto.lean              # Pareto optimality
│   ├── Liberalism.lean          # Minimal liberalism
│   └── Rationality.lean         # Rational social preference
└── Sen/
    └── BaseCase24/
        ├── Spec.lean            # Specification for n=2, m=4
        ├── Theorem.lean         # Main theorem statement
        ├── SAT.lean             # SAT encoding
        ├── SATSen.lean          # SAT verification
        └── SATSenGenerated.lean # Generated SAT proof
```

## Advantages of Certificate-Based Proofs

1. **Reproducibility**: The same certificate verifies on any machine with Lean 4
2. **Speed**: Verification is O(n) in certificate size, much faster than re-solving
3. **Trust**: Lean's kernel checks the proof, not the SAT solver
4. **Transparency**: The entire proof can be inspected and verified independently
5. **Extensibility**: Easy to add new base cases with different parameters

## Future Work

| Voters (n) | Alternatives (m) | Status      | Notes |
|------------|------------------|-------------|-------|
| 2          | 4                | ✓ Complete  | Current implementation |
| 2          | 5                | Planned     | Larger search space |
| 3          | 4                | Planned     | More complex interactions |

## Building and Verifying

### Prerequisites

- [Lean 4](https://leanprover.github.io/) (version specified in `lean-toolchain`)
- [Lake](https://github.com/leanprover/lake) (Lean's build system)

### Build Instructions

```bash
# Build the entire project
lake build

# Build only the Sen base case
lake build SocialChoiceAtlas.Sen.BaseCase24

# Build with SAT verification (slower, generates proof)
lake build SocialChoiceAtlas.Sen.BaseCase24.SATSenGenerated
```

## References

- Sen, A. K. (1970). "The Impossibility of a Paretian Liberal". *Journal of Political Economy*, 78(1), 152-157.
- [Lean 4 Documentation](https://leanprover.github.io/lean4/doc/)
- [Mathlib4](https://github.com/leanprover-community/mathlib4)

## License

This project is part of the SocialChoiceAtlas research effort exploring formal verification of social choice theory theorems.
| 3          | 5                | TODO   |

## Tools Required

- [CaDiCaL](https://github.com/arminbiere/cadical) - SAT solver with LRAT
- [DRAT-trim](https://github.com/marijnheule/drat-trim) - Certificate trimmer
- Python 3.x - For CNF encoding scripts

## References

- Heule, M. (2017). "The DRAT format and DRAT-trim checker"
- Lean 4 `bv_decide` documentation
- Geist, C. & Endriss, U. (2011). "Automated Search for Impossibility Theorems"
