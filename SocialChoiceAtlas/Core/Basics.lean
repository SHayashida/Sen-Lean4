/-
Copyright (c) 2025 SocialChoiceAtlas Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SocialChoiceAtlas Contributors
-/

/-!
# Core Relation Utilities

This module provides basic definitions for working with binary relations
in social choice theory: strict part, cycles, and acyclicity.
-/

namespace SocialChoiceAtlas

universe u
variable {α : Type u}

/-- The strict part of a binary relation R: x P y iff x R y and not y R x. -/
def strictPart (R : α → α → Prop) (x y : α) : Prop :=
  R x y ∧ ¬R y x

/-- Notation for strict part: `P R` is the strict part of R. -/
scoped notation "P " R => strictPart R

/-- A 3-cycle exists in a strict relation S. -/
def cycle3 (S : α → α → Prop) : Prop :=
  ∃ a b c, a ≠ b ∧ b ≠ c ∧ c ≠ a ∧ S a b ∧ S b c ∧ S c a

/-- Acyclicity (3-cycle version): no 3-cycle exists.
    This is sufficient for Sen's impossibility theorem. -/
def Acyclic (S : α → α → Prop) : Prop :=
  ¬∃ a b c, S a b ∧ S b c ∧ S c a

/-- A 3-cycle implies the relation is not acyclic. -/
theorem cycle3_implies_not_acyclic {S : α → α → Prop} (h : cycle3 S) : ¬Acyclic S := by
  intro hAcyclic
  unfold cycle3 at h
  rcases h with ⟨a, b, c, _, _, _, hab, hbc, hca⟩
  exact hAcyclic ⟨a, b, c, hab, hbc, hca⟩

/-- Irreflexivity of strict part follows from its definition. -/
theorem strictPart_irrefl (R : α → α → Prop) (x : α) : ¬strictPart R x x := by
  intro ⟨h, hn⟩
  exact hn h

/-- Asymmetry of strict part. -/
theorem strictPart_asymm (R : α → α → Prop) (x y : α) :
    strictPart R x y → ¬strictPart R y x := by
  intro hxy hyx
  exact hxy.2 hyx.1

end SocialChoiceAtlas
