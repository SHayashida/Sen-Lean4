/-
Copyright (c) 2026 SocialChoiceAtlas Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SocialChoiceAtlas Contributors
-/
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import SocialChoiceAtlas.Core.Basics
import SocialChoiceAtlas.Core.Ranking
import SocialChoiceAtlas.Core.Profile
import SocialChoiceAtlas.Axioms.Pareto
import SocialChoiceAtlas.Axioms.Liberalism
import SocialChoiceAtlas.Axioms.Rationality

/-!
# Sen's Impossibility — Lift from Base Case `(Fin 2, Fin 4)` to `(Fin n, Fin m)`

This module is the M2 Transfer-Contract deliverable in the Lean Proof layer.
The target theorem `sen_impossibility_lifts` (Stage 2) generalises
`SocialChoiceAtlas.Sen.BaseCase24.sen_impossibility_basecase` from the
finite case `(Voter := Fin 2, Alt := Fin 4)` to any finite case with
`2 ≤ n` voters and `4 ≤ m` alternatives, by direct semantic construction
on the strict social preference relation.

This file is the **Stage 1** commit: it contains the module shell,
imports, the namespace, and the single helper lemma `exists_not_mem_of_card_lt`
which is the technical core of the "completion lemma" named in the M2
prompt's obstacle section. Stage 2 will add the ranking-completion helper,
the profile lift, the polymorphic port of `sen_not_acyclic_01`, and the main
theorem.

The companion plan is `docs/gates/m2/impossibility_lift_stage1_plan.md`.
The scope wall (Proof layer vs. CNF Witness/Audit layer) is documented in
`docs/m2_scope_wall.md` (added at Stage 2 alongside the main proof).
-/

namespace SocialChoiceAtlas.Sen.Lifting

open SocialChoiceAtlas

/-! ### Completion-lemma core

The named obstacle in the M2 prompt: lifting Sen's base-case proof from
`(Fin 2, Fin 4)` to `(Fin n, Fin m)` requires that, given a small set of
already-distinguished alternatives in `Fin m` (≤ 3 in the 1-overlap subcase
of the 3-case analysis), we can extract a *fresh* alternative not in that
set, so that the cycle-pattern construction goes through. The mathematical
content reduces to the following Mathlib-style fact: a finset that is
strictly smaller than the ambient finite type has an element of the
ambient type outside it. -/

/--
If a `Finset α` over a `Fintype α` has cardinality strictly less than
`Fintype.card α`, then there exists an element of `α` not in the finset.

This is the polymorphic completion lemma used to obtain fresh alternatives
in `Fin m` from `4 ≤ m` (instantiated via `Fintype.card_fin`).
-/
lemma exists_not_mem_of_card_lt
    {α : Type*} [DecidableEq α] [Fintype α]
    {s : Finset α} (h : s.card < Fintype.card α) :
    ∃ a : α, a ∉ s := by
  have hne : s ≠ Finset.univ := (Finset.card_lt_iff_ne_univ s).mp h
  by_contra hall
  push_neg at hall
  apply hne
  apply Finset.eq_univ_iff_forall.mpr
  intro a
  exact hall a

end SocialChoiceAtlas.Sen.Lifting
