/-
Copyright (c) 2026 SocialChoiceAtlas Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SocialChoiceAtlas Contributors
-/
import Mathlib.Data.Finset.Card
import SocialChoiceAtlas.Core.Profile

/-!
# Generic Profiles for Sen Obstruction Soundness

This module provides the generic ranking and profile constructions needed for
the M2 finite-obstruction bridge Stage 2 soundness layer.

The construction is independent of `ImpossibilityLift.lean`: it repeats the
same prefix-ranking idea without importing the legacy lifting module, so the
new obstruction stack can remain non-circular. Stage 3 may consolidate the
legacy helper and this helper once `sen_impossibility_lifts` is refactored as
a corollary of the obstruction interface.

The profile construction is an ambient profile over an arbitrary voter type:
one distinguished voter `j` receives ranking `r_j`, and every other voter
receives ranking `r_i`. This is not an exactly-two-voter profile; it is a
profile using at most two ranking types. Consequently, unanimity edges are
still proved for all voters.
-/

namespace SocialChoiceAtlas.Sen

open SocialChoiceAtlas

universe u v

variable {Voter : Type u} {Alt : Type v} [DecidableEq Alt] [Fintype Alt]

/-- Append the finite complement of a prefix list to complete a ranking. -/
private noncomputable def obstructionExtendList (l : List Alt) : List Alt :=
  l ++ (Finset.univ \ l.toFinset).toList

private lemma obstructionExtendList_nodup
    (l : List Alt) (hnodup : l.Nodup) : (obstructionExtendList l).Nodup := by
  classical
  refine List.Nodup.append hnodup (Finset.nodup_toList _) ?_
  intro a ha hb
  have ha' : a ∈ l.toFinset := List.mem_toFinset.mpr ha
  have hb' : a ∈ (Finset.univ \ l.toFinset : Finset Alt) := Finset.mem_toList.mp hb
  exact (Finset.mem_sdiff.mp hb').2 ha'

private lemma obstructionExtendList_complete (l : List Alt) :
    ∀ a : Alt, a ∈ obstructionExtendList l := by
  classical
  intro a
  by_cases h : a ∈ l
  · exact List.mem_append_left _ h
  · refine List.mem_append_right _ ?_
    have ha : a ∈ (Finset.univ \ l.toFinset : Finset Alt) := by
      refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, ?_⟩
      intro hcontra
      exact h (List.mem_toFinset.mp hcontra)
    exact (Finset.mem_toList).mpr ha

/--
Ranking that begins with a caller-supplied `Nodup` prefix and then completes
with the remaining ambient alternatives in a fixed finite order.
-/
noncomputable def obstructionRankingOfPrefix
    (l : List Alt) (hnodup : l.Nodup) : Ranking Alt :=
  { toList := obstructionExtendList l
    nodup := obstructionExtendList_nodup l hnodup
    complete := obstructionExtendList_complete l }

/-- Prefix elements keep their prefix index in the completed ranking. -/
lemma obstructionRanking_position_of_mem_prefix
    (l : List Alt) (hnodup : l.Nodup) {a : Alt} (ha : a ∈ l) :
    (obstructionRankingOfPrefix l hnodup).position a = l.indexOf a := by
  classical
  show (obstructionExtendList l).indexOf a = l.indexOf a
  unfold obstructionExtendList
  exact List.indexOf_append_of_mem ha

/-- Positional version for `getElem`: the prefix position is exactly `k`. -/
lemma obstructionRanking_position_getElem
    (l : List Alt) (hnodup : l.Nodup) (k : ℕ) (h : k < l.length) :
    (obstructionRankingOfPrefix l hnodup).position l[k] = k := by
  classical
  have hmem : l[k] ∈ l := List.getElem_mem h
  rw [obstructionRanking_position_of_mem_prefix l hnodup hmem]
  exact List.indexOf_getElem hnodup k h

/--
If a prefix element occurs earlier than another prefix element, the completed
ranking strictly prefers the earlier element.
-/
lemma obstructionRanking_prefers_getElem
    (l : List Alt) (hnodup : l.Nodup)
    {i j : ℕ} (hi : i < l.length) (hj : j < l.length) (hij : i < j) :
    (obstructionRankingOfPrefix l hnodup).prefers l[i] l[j] := by
  unfold Ranking.prefers
  rw [obstructionRanking_position_getElem l hnodup i hi,
      obstructionRanking_position_getElem l hnodup j hj]
  exact hij

/--
Ambient two-ranking profile: voter `j` receives `r_j`; every other voter
receives `r_i`.
-/
noncomputable def twoRankingProfile
    (r_i r_j : Ranking Alt) (j : Voter) : Profile Voter Alt := by
  classical
  exact fun k => if k = j then r_j else r_i

@[simp] theorem twoRankingProfile_apply_j
    (r_i r_j : Ranking Alt) (j : Voter) :
    twoRankingProfile (Voter := Voter) r_i r_j j j = r_j := by
  classical
  simp [twoRankingProfile]

theorem twoRankingProfile_apply_ne
    (r_i r_j : Ranking Alt) {j k : Voter} (hkj : k ≠ j) :
    twoRankingProfile (Voter := Voter) r_i r_j j k = r_i := by
  classical
  simp [twoRankingProfile, hkj]

theorem prefers_i_twoRankingProfile_at_j
    (r_i r_j : Ranking Alt) (j : Voter) (a b : Alt) :
    prefers_i (twoRankingProfile (Voter := Voter) r_i r_j j) j a b ↔
      r_j.prefers a b := by
  unfold prefers_i
  simp

theorem prefers_i_twoRankingProfile_at_other
    (r_i r_j : Ranking Alt) {j k : Voter} (hkj : k ≠ j) (a b : Alt) :
    prefers_i (twoRankingProfile (Voter := Voter) r_i r_j j) k a b ↔
      r_i.prefers a b := by
  unfold prefers_i
  rw [twoRankingProfile_apply_ne r_i r_j hkj]

theorem prefers_i_twoRankingProfile_at_i
    {i j : Voter} (hij : i ≠ j) (r_i r_j : Ranking Alt) (a b : Alt) :
    prefers_i (twoRankingProfile (Voter := Voter) r_i r_j j) i a b ↔
      r_i.prefers a b :=
  prefers_i_twoRankingProfile_at_other (Voter := Voter) r_i r_j hij a b

/-- Unanimity over the ambient profile reduces to agreement by the two rankings. -/
theorem twoRankingProfile_unanimous
    (r_i r_j : Ranking Alt) (j : Voter) {a b : Alt}
    (hi : r_i.prefers a b) (hj : r_j.prefers a b) :
    ∀ k : Voter,
      prefers_i (twoRankingProfile (Voter := Voter) r_i r_j j) k a b := by
  classical
  intro k
  by_cases hkj : k = j
  · subst hkj
    exact (prefers_i_twoRankingProfile_at_j (Voter := Voter) r_i r_j k a b).mpr hj
  · exact (prefers_i_twoRankingProfile_at_other (Voter := Voter) r_i r_j hkj a b).mpr hi

end SocialChoiceAtlas.Sen
