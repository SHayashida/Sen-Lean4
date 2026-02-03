/-
Copyright (c) 2025 SocialChoiceAtlas Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SocialChoiceAtlas Contributors
-/
import SocialChoiceAtlas.Core.Basics
import SocialChoiceAtlas.Core.Profile

/-!
# Liberalism Axioms

Decisiveness and minimal liberalism as defined by Sen.

A voter i is decisive over a pair (x, y) if i's preference between x and y
always determines the social strict preference.

Minimal liberalism (MINLIB) requires at least two distinct voters,
each decisive over some pair.
-/

namespace SocialChoiceAtlas

universe u v
variable {Voter : Type u} {Alt : Type v} [DecidableEq Alt] [Fintype Alt]

/-- Voter i is decisive over the ordered pair (x, y) if:
    - when i prefers x to y, society strictly prefers x to y
    - when i prefers y to x, society strictly prefers y to x -/
def Decisive (F : SWF Voter Alt) (i : Voter) (x y : Alt) : Prop :=
  (∀ p, prefers_i p i x y → strictPart (F p) x y) ∧
  (∀ p, prefers_i p i y x → strictPart (F p) y x)

/-- Minimal liberalism: there exist two distinct voters, each decisive
    over some (possibly overlapping) pair of alternatives. -/
def MINLIB (F : SWF Voter Alt) : Prop :=
  ∃ i j : Voter, i ≠ j ∧
    ∃ x y : Alt, x ≠ y ∧ Decisive F i x y ∧
    ∃ z w : Alt, z ≠ w ∧ Decisive F j z w

/-- Symmetric decisiveness: decisive in both directions (convenience lemma). -/
theorem Decisive.symm {F : SWF Voter Alt} {i : Voter} {x y : Alt}
    (h : Decisive F i x y) : Decisive F i y x := by
  constructor <;> intro p hp
  · exact h.2 p hp
  · exact h.1 p hp

end SocialChoiceAtlas
