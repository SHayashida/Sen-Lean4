# SocialChoiceAtlas - Sen's Impossibility Theorem in Lean 4

Formal verification of Sen's "Impossibility of a Paretian Liberal" theorem using SAT-based proof certificates in Lean 4.

## Overview

This project formalizes and verifies Sen's classic impossibility theorem from social choice theory. We use SAT solvers to verify finite base cases, producing LRAT proof certificates that are checked by Lean 4's kernel for the highest level of mathematical rigor.

## Sen's Theorem

Sen's theorem states that there is no social decision function that simultaneously satisfies:
- **Pareto Optimality**: If all voters prefer x to y, society must prefer x to y
- **Minimal Liberalism**: Each voter is decisive on at least one pair of alternatives  
- **Rational Social Preference**: Social preferences form a transitive and complete ordering

## Repository Structure

```
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

Certificates/                    # LRAT proof certificates
scripts/
└── gen_sen24_sat.py            # Generates SAT encoding
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
- Python 3.x (for encoding generation)

### Build Instructions

```bash
# Build the entire project
lake build

# Build only the Sen base case
lake build SocialChoiceAtlas.Sen.BaseCase24

# Build with SAT verification (generates proof)
lake build SocialChoiceAtlas.Sen.BaseCase24.SATSenGenerated
```

### Verification Workflow

For detailed instructions on generating and caching LRAT certificates, see [Certificates/README.md](Certificates/README.md).

Quick overview:
1. Replace `bv_decide` with `bv_decide?` in the theorem
2. Run Lean with an absolute path to generate the `.lrat` file
3. Switch to `bv_check "certificate.lrat"` for fast verification
4. Commit the certificate to the repository

## References

- Sen, A. K. (1970). "The Impossibility of a Paretian Liberal". *Journal of Political Economy*, 78(1), 152-157.
- [Lean 4 Documentation](https://leanprover.github.io/lean4/doc/)
- [Mathlib4](https://github.com/leanprover-community/mathlib4)
- Heule, M. (2017). "The DRAT format and DRAT-trim checker"
- Geist, C. & Endriss, U. (2011). "Automated Search for Impossibility Theorems in Social Choice Theory"

## License

This project is part of the SocialChoiceAtlas research effort exploring formal verification of social choice theory theorems.
