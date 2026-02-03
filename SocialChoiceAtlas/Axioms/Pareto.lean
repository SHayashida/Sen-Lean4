/-
Copyright (c) 2025 SocialChoiceAtlas Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SocialChoiceAtlas Contributors
-/
import SocialChoiceAtlas.Core.Basics
import SocialChoiceAtlas.Core.Profile

/-!
# Pareto Axiom (Unanimity)

The weak Pareto principle (UN): if all voters strictly prefer x to y,
then society strictly prefers x to y.
-/

namespace SocialChoiceAtlas

universe u v
variable {Voter : Type u} {Alt : Type v} [DecidableEq Alt] [Fintype Alt]

/-- Unanimity (Weak Pareto): if all voters prefer x to y, society's strict
    preference ranks x above y. -/
def UN (F : SWF Voter Alt) : Prop :=
  ∀ p x y, (∀ i, prefers_i p i x y) → strictPart (F p) x y

end SocialChoiceAtlas
