/-
Proof-carrying UNSAT verification for atlas case `case_11111` (sen24).

Build with:
  `lake build SocialChoiceAtlas.Sen.Atlas.Case11111`
-/
import Mathlib.Tactic.Sat.FromLRAT

namespace SocialChoiceAtlas.Sen.Atlas

lrat_proof case11111_unsat_cnf
  (include_str "../../../Certificates/atlas/case_11111/sen24.cnf")
  (include_str "../../../Certificates/atlas/case_11111/proof.lrat")

theorem case11111_cnf_unsat :
    ¬ ∃ v : Sat.Valuation, Sat.Valuation.satisfies_fmla v case11111_unsat_cnf.ctx_1 := by
  intro h
  rcases h with ⟨v, hv⟩
  have hproof : Sat.Fmla.proof case11111_unsat_cnf.ctx_1 [] := case11111_unsat_cnf.proof_1
  have : Sat.Valuation.satisfies v [] := hproof v hv
  cases this

end SocialChoiceAtlas.Sen.Atlas
