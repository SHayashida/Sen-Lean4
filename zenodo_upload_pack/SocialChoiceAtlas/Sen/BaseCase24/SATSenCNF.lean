/-
Certified UNSAT check of the Sen (n=2, m=4) base case using DIMACS CNF + LRAT.

Build just this module with:
  `lake build SocialChoiceAtlas.Sen.BaseCase24.SATSenCNF`
-/
import Mathlib.Tactic.Sat.FromLRAT

namespace SocialChoiceAtlas.Sen.BaseCase24

-- The certificate files live in `Certificates/` at the repo root.
-- `include_str` reads them at compile time and `lrat_proof` checks LRAT in the Lean kernel.
lrat_proof sen24_unsat_cnf
  (include_str "../../../Certificates/sen24.cnf")
  (include_str "../../../Certificates/sen24.lrat")

-- A more direct "UNSAT" statement, derived from the checked LRAT proof object.
theorem sen24_cnf_unsat :
    ¬ ∃ v : Sat.Valuation, Sat.Valuation.satisfies_fmla v sen24_unsat_cnf.ctx_1 := by
  intro h
  rcases h with ⟨v, hv⟩
  have hproof : Sat.Fmla.proof sen24_unsat_cnf.ctx_1 [] := sen24_unsat_cnf.proof_1
  have : Sat.Valuation.satisfies v [] := hproof v hv
  cases this

end SocialChoiceAtlas.Sen.BaseCase24

