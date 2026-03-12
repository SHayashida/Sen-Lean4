/-
Copyright (c) 2025 SocialChoiceAtlas Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SocialChoiceAtlas Contributors
-/
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.List.Dedup
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Perm.Basic

/-!
# Rankings (Total Orders as Permutations)

A ranking over a finite type is represented as a list with no duplicates
that contains all elements. The preference relation is defined by position:
x is preferred to y iff x appears before y in the list.
-/

namespace SocialChoiceAtlas

universe u
variable {α : Type u} [DecidableEq α] [Fintype α]

/-- A ranking is a list that is a permutation of all elements (nodup + complete). -/
structure Ranking (α : Type u) [DecidableEq α] [Fintype α] where
  toList : List α
  nodup : toList.Nodup
  complete : ∀ a : α, a ∈ toList

namespace Ranking

variable {α : Type u} [DecidableEq α] [Fintype α]

/-- Get the position (0-indexed) of an element in the ranking. -/
def position (r : Ranking α) (x : α) : ℕ :=
  r.toList.indexOf x

/-- x is strictly preferred to y in ranking r iff x appears before y. -/
def prefers (r : Ranking α) (x y : α) : Prop :=
  r.position x < r.position y

instance decidablePrefers (r : Ranking α) (x y : α) : Decidable (r.prefers x y) :=
  inferInstanceAs (Decidable (_ < _))

/-- Preference is irreflexive. -/
theorem prefers_irrefl (r : Ranking α) (x : α) : ¬r.prefers x x := by
  unfold prefers
  exact Nat.lt_irrefl _

/-- Preference is transitive. -/
theorem prefers_trans (r : Ranking α) {x y z : α} :
    r.prefers x y → r.prefers y z → r.prefers x z := by
  unfold prefers
  exact Nat.lt_trans

/-- Preference is asymmetric. -/
theorem prefers_asymm (r : Ranking α) {x y : α} :
    r.prefers x y → ¬r.prefers y x := by
  unfold prefers
  exact fun h1 h2 => Nat.lt_asymm h1 h2

/-- Preference is total for distinct elements. -/
theorem prefers_total (r : Ranking α) {x y : α} (hne : x ≠ y) :
    r.prefers x y ∨ r.prefers y x := by
  unfold prefers
  have hx := r.complete x
  have hy := r.complete y
  have hxpos := List.indexOf_lt_length.mpr hx
  have hypos := List.indexOf_lt_length.mpr hy
  by_cases h : r.position x < r.position y
  · left; exact h
  · right
    push_neg at h
    cases Nat.lt_or_eq_of_le h with
    | inl hlt => exact hlt
    | inr heq =>
      exfalso
      unfold position at heq
      have hyx : y = x := (List.indexOf_inj hy hx).1 heq
      exact hne hyx.symm

/-- The length of a ranking equals the cardinality of the type. -/
theorem length_eq_card (r : Ranking α) : r.toList.length = Fintype.card α := by
  classical
  have huniv : r.toList.toFinset = Finset.univ := by
    ext a
    constructor
    · intro _
      simp
    · intro _
      exact (List.mem_toFinset).2 (r.complete a)
  calc
    r.toList.length = r.toList.toFinset.card := by
      simpa using (List.toFinset_card_of_nodup (l := r.toList) r.nodup).symm
    _ = Finset.univ.card := by simp [huniv]
    _ = Fintype.card α := rfl

end Ranking

end SocialChoiceAtlas
