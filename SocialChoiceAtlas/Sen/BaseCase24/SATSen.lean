/-
SAT-backed (LRAT) verification for Sen's base case (n=2, m=4).

This module is intentionally independent from the constructive proof in
`SocialChoiceAtlas/Sen/BaseCase24/Theorem.lean`.

Build just this module with:
  `lake build SocialChoiceAtlas.Sen.BaseCase24.SATSen`
-/
import SocialChoiceAtlas.Sen.BaseCase24.SATSenCNF

-- Re-export via import only; `sen24_cnf_unsat` is in namespace `SocialChoiceAtlas.Sen.BaseCase24`.
