/-
Copyright (c) 2025 SocialChoiceAtlas Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SocialChoiceAtlas Contributors
-/
import SocialChoiceAtlas.Core.Basics
import SocialChoiceAtlas.Core.Profile

/-!
# Rationality Axioms

Rationality conditions on social welfare functions:
- Acyclicity of the social strict preference
- Transitivity (optional, stronger)
- Totality / Completeness (optional)
-/

namespace SocialChoiceAtlas

universe u v
variable {Voter : Type u} {Alt : Type v} [DecidableEq Alt] [Fintype Alt]

/-- Social acyclicity: for all profiles, the strict part of F(p) is acyclic. -/
def SocialAcyclic (F : SWF Voter Alt) : Prop :=
  ∀ p, Acyclic (strictPart (F p))

/-- Social transitivity: the strict part is transitive for all profiles. -/
def SocialTransitive (F : SWF Voter Alt) : Prop :=
  ∀ p x y z, strictPart (F p) x y → strictPart (F p) y z → strictPart (F p) x z

/-- Totality: for distinct alternatives, either x R y or y R x. -/
def SocialTotal (F : SWF Voter Alt) : Prop :=
  ∀ p x y, x ≠ y → F p x y ∨ F p y x

/-- Transitivity implies acyclicity for strict relations. -/
theorem SocialTransitive.toAcyclic {F : SWF Voter Alt}
    (hTrans : SocialTransitive F) : SocialAcyclic F := by
  intro p
  unfold Acyclic
  push_neg
  intro a b c hab hbc hca
  have hac := hTrans p a b c hab hbc
  have haa := hTrans p a c a hac hca
  exact strictPart_irrefl (F p) a haa

end SocialChoiceAtlas
