/-
Copyright (c) 2026 SocialChoiceAtlas Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SocialChoiceAtlas Contributors
-/
import SocialChoiceAtlas.Sen.ObstructionBasis
import SocialChoiceAtlas.Sen.ObstructionProfiles
import SocialChoiceAtlas.Axioms.Pareto
import SocialChoiceAtlas.Axioms.Rationality

/-!
# Sen Obstruction Soundness, Stage 2

This module proves semantic soundness for the O2/O3/O4 overlap shapes exposed
by `SocialChoiceAtlas.Sen.ObstructionBasis`.

* O2 yields a strict social conflict.
* O3 yields a 3-cycle.
* O4 yields a 4-cycle.

The result is semantic: it is not a CNF, LRAT, Sen24 atlas, literal two-voter
restriction, or repair/MCS theorem. It does not compose `MINLIB` extraction
with soundness into the final Sen impossibility theorem; that is reserved for
Stage 3. This module also does not import `ImpossibilityLift.lean` or the
Sen24 base-case theorem.
-/

namespace SocialChoiceAtlas.Sen

open SocialChoiceAtlas

universe u v

variable {Voter : Type u} {Alt : Type v} [DecidableEq Alt] [Fintype Alt]

namespace SenRightsWitness

/-- Reverse the orientation of the second decisive pair. -/
def swapSecondPair {F : SWF Voter Alt} (wit : SenRightsWitness F) :
    SenRightsWitness F :=
  { i := wit.i
    j := wit.j
    i_ne_j := wit.i_ne_j
    x := wit.x
    y := wit.y
    z := wit.w
    w := wit.z
    x_ne_y := wit.x_ne_y
    z_ne_w := wit.z_ne_w.symm
    decisive_i := wit.decisive_i
    decisive_j := wit.decisive_j.symm }

/-- O2 support has exactly two alternatives. -/
theorem support_card_eq_two_of_twoOverlap {F : SWF Voter Alt}
    (wit : SenRightsWitness F)
    (hz : wit.z ∈ ({wit.x, wit.y} : Finset Alt))
    (hw : wit.w ∈ ({wit.x, wit.y} : Finset Alt)) :
    wit.support.card = 2 := by
  classical
  have hz' : wit.z = wit.x ∨ wit.z = wit.y := by simpa using hz
  have hw' : wit.w = wit.x ∨ wit.w = wit.y := by simpa using hw
  rcases hz' with hzx | hzy
  · rcases hw' with hwx | hwy
    · exact False.elim (wit.z_ne_w (hzx.trans hwx.symm))
    · simpa [support, hzx, hwy] using
        (Finset.card_pair (a := wit.x) (b := wit.y) wit.x_ne_y)
  · rcases hw' with hwx | hwy
    · simpa [support, hzy, hwx] using
        (Finset.card_pair (a := wit.y) (b := wit.x) wit.x_ne_y.symm)
    · exact False.elim (wit.z_ne_w (hzy.trans hwy.symm))

/-- Raw z-only O3 support has exactly three alternatives. -/
theorem support_card_eq_three_of_zOnly {F : SWF Voter Alt}
    (wit : SenRightsWitness F)
    (hz : wit.z ∈ ({wit.x, wit.y} : Finset Alt))
    (hw : wit.w ∉ ({wit.x, wit.y} : Finset Alt)) :
    wit.support.card = 3 := by
  classical
  have hz' : wit.z = wit.x ∨ wit.z = wit.y := by simpa using hz
  have hwx : wit.w ≠ wit.x := by
    intro h
    exact hw (by simp [h])
  have hwy : wit.w ≠ wit.y := by
    intro h
    exact hw (by simp [h])
  rcases hz' with hzx | hzy
  · have hcard :
        ({wit.x, wit.y, wit.w} : Finset Alt).card = 3 := by
      rw [Finset.card_insert_of_not_mem]
      · rw [Finset.card_pair (a := wit.y) (b := wit.w) hwy.symm]
      · simp [wit.x_ne_y, hwx.symm]
    simpa [support, hzx, Finset.insert_comm] using hcard
  · have hcard :
        ({wit.x, wit.y, wit.w} : Finset Alt).card = 3 := by
      rw [Finset.card_insert_of_not_mem]
      · rw [Finset.card_pair (a := wit.y) (b := wit.w) hwy.symm]
      · simp [wit.x_ne_y, hwx.symm]
    simpa [support, hzy, Finset.insert_comm] using hcard

/-- Raw w-only O3 support has exactly three alternatives. -/
theorem support_card_eq_three_of_wOnly {F : SWF Voter Alt}
    (wit : SenRightsWitness F)
    (hz : wit.z ∉ ({wit.x, wit.y} : Finset Alt))
    (hw : wit.w ∈ ({wit.x, wit.y} : Finset Alt)) :
    wit.support.card = 3 := by
  classical
  have hw' : wit.w = wit.x ∨ wit.w = wit.y := by simpa using hw
  have hzx : wit.z ≠ wit.x := by
    intro h
    exact hz (by simp [h])
  have hzy : wit.z ≠ wit.y := by
    intro h
    exact hz (by simp [h])
  rcases hw' with hwx | hwy
  · have hcard :
        ({wit.y, wit.z, wit.x} : Finset Alt).card = 3 := by
      rw [Finset.card_insert_of_not_mem]
      · rw [Finset.card_pair (a := wit.z) (b := wit.x) hzx]
      · simp [wit.x_ne_y.symm, hzy.symm]
    simpa [support, hwx] using hcard
  · have hcard :
        ({wit.x, wit.z, wit.y} : Finset Alt).card = 3 := by
      rw [Finset.card_insert_of_not_mem]
      · rw [Finset.card_pair (a := wit.z) (b := wit.y) hzy]
      · simp [wit.x_ne_y, hzx.symm]
    simpa [support, hwy] using hcard

/-- O4 support has exactly four alternatives. -/
theorem support_card_eq_four_of_disjoint {F : SWF Voter Alt}
    (wit : SenRightsWitness F)
    (hz : wit.z ∉ ({wit.x, wit.y} : Finset Alt))
    (hw : wit.w ∉ ({wit.x, wit.y} : Finset Alt)) :
    wit.support.card = 4 := by
  classical
  have hzx : wit.z ≠ wit.x := by intro h; exact hz (by simp [h])
  have hzy : wit.z ≠ wit.y := by intro h; exact hz (by simp [h])
  have hwx : wit.w ≠ wit.x := by intro h; exact hw (by simp [h])
  have hwy : wit.w ≠ wit.y := by intro h; exact hw (by simp [h])
  rw [support]
  rw [Finset.card_insert_of_not_mem]
  · rw [Finset.card_insert_of_not_mem]
    · rw [Finset.card_insert_of_not_mem]
      · rw [Finset.card_singleton]
      · simp [wit.z_ne_w]
    · simp [hzy.symm, hwy.symm]
  · simp [wit.x_ne_y, hzx.symm, hwx.symm]

end SenRightsWitness

namespace ClassifiedSenRightsWitness

/-- Classified witnesses have the exact support cardinality indicated by O2/O3/O4. -/
theorem support_card_eq_kind {F : SWF Voter Alt} (cw : ClassifiedSenRightsWitness F) :
    cw.support.card =
      match cw.kind with
      | SenObstructionShape.O2 => 2
      | SenObstructionShape.O3 => 3
      | SenObstructionShape.O4 => 4 := by
  cases cw with
  | mk wit rawShape =>
    cases rawShape with
    | twoOverlap hz hw =>
        exact wit.support_card_eq_two_of_twoOverlap hz hw
    | zOnly hz hw =>
        exact wit.support_card_eq_three_of_zOnly hz hw
    | wOnly hz hw =>
        exact wit.support_card_eq_three_of_wOnly hz hw
    | disjoint hz hw =>
        exact wit.support_card_eq_four_of_disjoint hz hw

end ClassifiedSenRightsWitness

/-- Semantic obstruction produced by a classified Sen witness shape. -/
inductive SenOutcomeObstruction (F : SWF Voter Alt) : Prop where
  | strictConflict
      (p : Profile Voter Alt)
      (a b : Alt)
      (hab : strictPart (F p) a b)
      (hba : strictPart (F p) b a)
  | cycle3At
      (p : Profile Voter Alt)
      (hcycle : cycle3 (strictPart (F p)))
  | cycle4At
      (p : Profile Voter Alt)
      (hcycle : cycle4 (strictPart (F p)))

namespace SenOutcomeObstruction

/-- Any semantic Sen outcome obstruction refutes social acyclicity. -/
theorem refutes_socialAcyclic {F : SWF Voter Alt}
    (o : SenOutcomeObstruction F) :
    ¬ SocialAcyclic F := by
  intro hAcyclic
  cases o with
  | strictConflict p a b hab hba =>
      exact strictPart_asymm (R := F p) a b hab hba
  | cycle3At p hcycle =>
      exact (cycle3_implies_not_acyclic hcycle) (hAcyclic p)
  | cycle4At p hcycle =>
      exact (cycle4_implies_not_acyclic hcycle) (hAcyclic p)

end SenOutcomeObstruction

private theorem twoOverlap_eq {F : SWF Voter Alt}
    (wit : SenRightsWitness F)
    (hz : wit.z ∈ ({wit.x, wit.y} : Finset Alt))
    (hw : wit.w ∈ ({wit.x, wit.y} : Finset Alt)) :
    (wit.z = wit.x ∧ wit.w = wit.y) ∨
      (wit.z = wit.y ∧ wit.w = wit.x) := by
  classical
  have hz' : wit.z = wit.x ∨ wit.z = wit.y := by simpa using hz
  have hw' : wit.w = wit.x ∨ wit.w = wit.y := by simpa using hw
  rcases hz' with hzx | hzy
  · rcases hw' with hwx | hwy
    · exact False.elim (wit.z_ne_w (hzx.trans hwx.symm))
    · exact Or.inl ⟨hzx, hwy⟩
  · rcases hw' with hwx | hwy
    · exact Or.inr ⟨hzy, hwx⟩
    · exact False.elim (wit.z_ne_w (hzy.trans hwy.symm))

/-- O2 soundness: two-overlap produces a strict social conflict. -/
theorem outcome_of_twoOverlap
    (F : SWF Voter Alt)
    (wit : SenRightsWitness F)
    (hz : wit.z ∈ ({wit.x, wit.y} : Finset Alt))
    (hw : wit.w ∈ ({wit.x, wit.y} : Finset Alt)) :
    SenOutcomeObstruction F := by
  classical
  have hzw_eq := twoOverlap_eq wit hz hw
  have hnodup_xy : ([wit.x, wit.y] : List Alt).Nodup := by simp [wit.x_ne_y]
  have hnodup_yx : ([wit.y, wit.x] : List Alt).Nodup := by simp [wit.x_ne_y.symm]
  let r_i : Ranking Alt := obstructionRankingOfPrefix [wit.x, wit.y] hnodup_xy
  let r_j : Ranking Alt := obstructionRankingOfPrefix [wit.y, wit.x] hnodup_yx
  let p : Profile Voter Alt := twoRankingProfile r_i r_j wit.j
  have hri_xy : r_i.prefers wit.x wit.y :=
    obstructionRanking_prefers_getElem (l := [wit.x, wit.y]) hnodup_xy
      (i := 0) (j := 1) (by simp) (by simp) (by decide)
  have h_i_xy : prefers_i p wit.i wit.x wit.y :=
    (prefers_i_twoRankingProfile_at_i wit.i_ne_j r_i r_j wit.x wit.y).mpr hri_xy
  have hrj_yx : r_j.prefers wit.y wit.x :=
    obstructionRanking_prefers_getElem (l := [wit.y, wit.x]) hnodup_yx
      (i := 0) (j := 1) (by simp) (by simp) (by decide)
  have h_j_yx : prefers_i p wit.j wit.y wit.x :=
    (prefers_i_twoRankingProfile_at_j r_i r_j wit.j wit.y wit.x).mpr hrj_yx
  have hxPy : strictPart (F p) wit.x wit.y := (wit.decisive_i p).1 h_i_xy
  have hyPx : strictPart (F p) wit.y wit.x := by
    rcases hzw_eq with ⟨hzx, hwy⟩ | ⟨hzy, hwx⟩
    · have h_pref : prefers_i p wit.j wit.w wit.z := by
        simpa [hzx, hwy] using h_j_yx
      have hstrict : strictPart (F p) wit.w wit.z := (wit.decisive_j p).2 h_pref
      simpa [hzx, hwy] using hstrict
    · have h_pref : prefers_i p wit.j wit.z wit.w := by
        simpa [hzy, hwx] using h_j_yx
      have hstrict : strictPart (F p) wit.z wit.w := (wit.decisive_j p).1 h_pref
      simpa [hzy, hwx] using hstrict
  exact SenOutcomeObstruction.strictConflict p wit.x wit.y hxPy hyPx

private theorem outcome_oneOverlap_shared_x
    (F : SWF Voter Alt)
    (hUN : UN F)
    (wit : SenRightsWitness F)
    {x y w : Alt}
    (hxy : x ≠ y)
    (hxw : x ≠ w)
    (hwy : w ≠ y)
    (hdec_i : Decisive F wit.i x y)
    (hdec_j : Decisive F wit.j x w) :
    SenOutcomeObstruction F := by
  classical
  have hwx : w ≠ x := hxw.symm
  have hnodup_i : ([w, y, x] : List Alt).Nodup := by simp [hwy, hwx, hxy.symm]
  have hnodup_j : ([x, w, y] : List Alt).Nodup := by simp [hxw, hxy, hwy]
  let r_i : Ranking Alt := obstructionRankingOfPrefix [w, y, x] hnodup_i
  let r_j : Ranking Alt := obstructionRankingOfPrefix [x, w, y] hnodup_j
  let p : Profile Voter Alt := twoRankingProfile r_i r_j wit.j
  have hri_yx : r_i.prefers y x :=
    obstructionRanking_prefers_getElem (l := [w, y, x]) hnodup_i
      (i := 1) (j := 2) (by simp) (by simp) (by decide)
  have h_i_yx : prefers_i p wit.i y x :=
    (prefers_i_twoRankingProfile_at_i wit.i_ne_j r_i r_j y x).mpr hri_yx
  have hrj_xw : r_j.prefers x w :=
    obstructionRanking_prefers_getElem (l := [x, w, y]) hnodup_j
      (i := 0) (j := 1) (by simp) (by simp) (by decide)
  have h_j_xw : prefers_i p wit.j x w :=
    (prefers_i_twoRankingProfile_at_j r_i r_j wit.j x w).mpr hrj_xw
  have hri_wy : r_i.prefers w y :=
    obstructionRanking_prefers_getElem (l := [w, y, x]) hnodup_i
      (i := 0) (j := 1) (by simp) (by simp) (by decide)
  have hrj_wy : r_j.prefers w y :=
    obstructionRanking_prefers_getElem (l := [x, w, y]) hnodup_j
      (i := 1) (j := 2) (by simp) (by simp) (by decide)
  have hall_wy : ∀ k : Voter, prefers_i p k w y :=
    twoRankingProfile_unanimous r_i r_j wit.j hri_wy hrj_wy
  have hyPx : strictPart (F p) y x := (hdec_i p).2 h_i_yx
  have hxPw : strictPart (F p) x w := (hdec_j p).1 h_j_xw
  have hwPy : strictPart (F p) w y := hUN p w y hall_wy
  have hcycle : cycle3 (strictPart (F p)) :=
    ⟨y, x, w, hxy.symm, hwx.symm, hwy, hyPx, hxPw, hwPy⟩
  exact SenOutcomeObstruction.cycle3At p hcycle

private theorem outcome_oneOverlap_shared_y
    (F : SWF Voter Alt)
    (hUN : UN F)
    (wit : SenRightsWitness F)
    {x y w : Alt}
    (hxy : x ≠ y)
    (hyw : y ≠ w)
    (hwx : w ≠ x)
    (hdec_i : Decisive F wit.i x y)
    (hdec_j : Decisive F wit.j y w) :
    SenOutcomeObstruction F := by
  classical
  have hwy : w ≠ y := hyw.symm
  have hnodup_i : ([w, x, y] : List Alt).Nodup := by simp [hwx, hwy, hxy]
  have hnodup_j : ([y, w, x] : List Alt).Nodup := by simp [hyw, hxy.symm, hwx]
  let r_i : Ranking Alt := obstructionRankingOfPrefix [w, x, y] hnodup_i
  let r_j : Ranking Alt := obstructionRankingOfPrefix [y, w, x] hnodup_j
  let p : Profile Voter Alt := twoRankingProfile r_i r_j wit.j
  have hri_xy : r_i.prefers x y :=
    obstructionRanking_prefers_getElem (l := [w, x, y]) hnodup_i
      (i := 1) (j := 2) (by simp) (by simp) (by decide)
  have h_i_xy : prefers_i p wit.i x y :=
    (prefers_i_twoRankingProfile_at_i wit.i_ne_j r_i r_j x y).mpr hri_xy
  have hrj_yw : r_j.prefers y w :=
    obstructionRanking_prefers_getElem (l := [y, w, x]) hnodup_j
      (i := 0) (j := 1) (by simp) (by simp) (by decide)
  have h_j_yw : prefers_i p wit.j y w :=
    (prefers_i_twoRankingProfile_at_j r_i r_j wit.j y w).mpr hrj_yw
  have hri_wx : r_i.prefers w x :=
    obstructionRanking_prefers_getElem (l := [w, x, y]) hnodup_i
      (i := 0) (j := 1) (by simp) (by simp) (by decide)
  have hrj_wx : r_j.prefers w x :=
    obstructionRanking_prefers_getElem (l := [y, w, x]) hnodup_j
      (i := 1) (j := 2) (by simp) (by simp) (by decide)
  have hall_wx : ∀ k : Voter, prefers_i p k w x :=
    twoRankingProfile_unanimous r_i r_j wit.j hri_wx hrj_wx
  have hxPy : strictPart (F p) x y := (hdec_i p).1 h_i_xy
  have hyPw : strictPart (F p) y w := (hdec_j p).1 h_j_yw
  have hwPx : strictPart (F p) w x := hUN p w x hall_wx
  have hcycle : cycle3 (strictPart (F p)) :=
    ⟨x, y, w, hxy, hwy.symm, hwx, hxPy, hyPw, hwPx⟩
  exact SenOutcomeObstruction.cycle3At p hcycle

/-- O3 z-only soundness: one endpoint shared as `z` produces a 3-cycle. -/
theorem outcome_of_zOnly
    (F : SWF Voter Alt)
    (hUN : UN F)
    (wit : SenRightsWitness F)
    (hz : wit.z ∈ ({wit.x, wit.y} : Finset Alt))
    (hw : wit.w ∉ ({wit.x, wit.y} : Finset Alt)) :
    SenOutcomeObstruction F := by
  classical
  have hz' : wit.z = wit.x ∨ wit.z = wit.y := by simpa using hz
  have hwx : wit.w ≠ wit.x := by intro h; exact hw (by simp [h])
  have hwy : wit.w ≠ wit.y := by intro h; exact hw (by simp [h])
  rcases hz' with hzx | hzy
  · have hxw : wit.x ≠ wit.w := by intro h; exact hwx h.symm
    have hdec_j' : Decisive F wit.j wit.x wit.w := by
      simpa [hzx] using wit.decisive_j
    exact outcome_oneOverlap_shared_x F hUN wit wit.x_ne_y hxw hwy wit.decisive_i hdec_j'
  · have hyw : wit.y ≠ wit.w := by intro h; exact hwy h.symm
    have hdec_j' : Decisive F wit.j wit.y wit.w := by
      simpa [hzy] using wit.decisive_j
    exact outcome_oneOverlap_shared_y F hUN wit wit.x_ne_y hyw hwx wit.decisive_i hdec_j'

/-- O3 w-only soundness, reduced to z-only by reversing the second decisive pair. -/
theorem outcome_of_wOnly
    (F : SWF Voter Alt)
    (hUN : UN F)
    (wit : SenRightsWitness F)
    (hz : wit.z ∉ ({wit.x, wit.y} : Finset Alt))
    (hw : wit.w ∈ ({wit.x, wit.y} : Finset Alt)) :
    SenOutcomeObstruction F := by
  classical
  let wit' := wit.swapSecondPair
  exact outcome_of_zOnly F hUN wit' hw hz

/-- O4 soundness: disjoint decisive pairs produce a 4-cycle. -/
theorem outcome_of_disjoint
    (F : SWF Voter Alt)
    (hUN : UN F)
    (wit : SenRightsWitness F)
    (hz : wit.z ∉ ({wit.x, wit.y} : Finset Alt))
    (hw : wit.w ∉ ({wit.x, wit.y} : Finset Alt)) :
    SenOutcomeObstruction F := by
  classical
  have hzx : wit.z ≠ wit.x := by intro h; exact hz (by simp [h])
  have hzy : wit.z ≠ wit.y := by intro h; exact hz (by simp [h])
  have hwx : wit.w ≠ wit.x := by intro h; exact hw (by simp [h])
  have hwy : wit.w ≠ wit.y := by intro h; exact hw (by simp [h])
  have hnodup_i : ([wit.w, wit.x, wit.y, wit.z] : List Alt).Nodup := by
    simp [hwx, hwy, wit.x_ne_y, hzx.symm, hzy.symm, wit.z_ne_w.symm]
  have hnodup_j : ([wit.y, wit.z, wit.w, wit.x] : List Alt).Nodup := by
    simp [wit.x_ne_y, wit.x_ne_y.symm, hzy, hzy.symm, hwx, hwx.symm,
      wit.z_ne_w, hwy, hwy.symm, hzx, hzx.symm]
  let r_i : Ranking Alt := obstructionRankingOfPrefix [wit.w, wit.x, wit.y, wit.z] hnodup_i
  let r_j : Ranking Alt := obstructionRankingOfPrefix [wit.y, wit.z, wit.w, wit.x] hnodup_j
  let p : Profile Voter Alt := twoRankingProfile r_i r_j wit.j
  have hri_xy : r_i.prefers wit.x wit.y :=
    obstructionRanking_prefers_getElem (l := [wit.w, wit.x, wit.y, wit.z]) hnodup_i
      (i := 1) (j := 2) (by simp) (by simp) (by decide)
  have h_i_xy : prefers_i p wit.i wit.x wit.y :=
    (prefers_i_twoRankingProfile_at_i wit.i_ne_j r_i r_j wit.x wit.y).mpr hri_xy
  have hrj_zw : r_j.prefers wit.z wit.w :=
    obstructionRanking_prefers_getElem (l := [wit.y, wit.z, wit.w, wit.x]) hnodup_j
      (i := 1) (j := 2) (by simp) (by simp) (by decide)
  have h_j_zw : prefers_i p wit.j wit.z wit.w :=
    (prefers_i_twoRankingProfile_at_j r_i r_j wit.j wit.z wit.w).mpr hrj_zw
  have hri_yz : r_i.prefers wit.y wit.z :=
    obstructionRanking_prefers_getElem (l := [wit.w, wit.x, wit.y, wit.z]) hnodup_i
      (i := 2) (j := 3) (by simp) (by simp) (by decide)
  have hrj_yz : r_j.prefers wit.y wit.z :=
    obstructionRanking_prefers_getElem (l := [wit.y, wit.z, wit.w, wit.x]) hnodup_j
      (i := 0) (j := 1) (by simp) (by simp) (by decide)
  have hall_yz : ∀ k : Voter, prefers_i p k wit.y wit.z :=
    twoRankingProfile_unanimous r_i r_j wit.j hri_yz hrj_yz
  have hri_wx : r_i.prefers wit.w wit.x :=
    obstructionRanking_prefers_getElem (l := [wit.w, wit.x, wit.y, wit.z]) hnodup_i
      (i := 0) (j := 1) (by simp) (by simp) (by decide)
  have hrj_wx : r_j.prefers wit.w wit.x :=
    obstructionRanking_prefers_getElem (l := [wit.y, wit.z, wit.w, wit.x]) hnodup_j
      (i := 2) (j := 3) (by simp) (by simp) (by decide)
  have hall_wx : ∀ k : Voter, prefers_i p k wit.w wit.x :=
    twoRankingProfile_unanimous r_i r_j wit.j hri_wx hrj_wx
  have hxPy : strictPart (F p) wit.x wit.y := (wit.decisive_i p).1 h_i_xy
  have hyPz : strictPart (F p) wit.y wit.z := hUN p wit.y wit.z hall_yz
  have hzPw : strictPart (F p) wit.z wit.w := (wit.decisive_j p).1 h_j_zw
  have hwPx : strictPart (F p) wit.w wit.x := hUN p wit.w wit.x hall_wx
  have hcycle : cycle4 (strictPart (F p)) :=
    ⟨wit.x, wit.y, wit.z, wit.w, wit.x_ne_y, hzy.symm, wit.z_ne_w, hwx,
      hxPy, hyPz, hzPw, hwPx⟩
  exact SenOutcomeObstruction.cycle4At p hcycle

/-- Raw overlap-shape soundness dispatcher. -/
theorem outcome_of_rawShape
    (F : SWF Voter Alt)
    (hUN : UN F)
    (wit : SenRightsWitness F)
    (shape : SenRawOverlapShape wit.x wit.y wit.z wit.w) :
    SenOutcomeObstruction F := by
  cases shape with
  | twoOverlap hz hw => exact outcome_of_twoOverlap F wit hz hw
  | zOnly hz hw => exact outcome_of_zOnly F hUN wit hz hw
  | wOnly hz hw => exact outcome_of_wOnly F hUN wit hz hw
  | disjoint hz hw => exact outcome_of_disjoint F hUN wit hz hw

/-- Stage-2 flagship: classified witnesses soundly produce semantic obstructions. -/
theorem outcome_of_classifiedWitness
    (F : SWF Voter Alt)
    (hUN : UN F)
    (cw : ClassifiedSenRightsWitness F) :
    SenOutcomeObstruction F :=
  outcome_of_rawShape F hUN cw.witness cw.rawShape

/--
Classified witness soundness composed with outcome refutation.

Stage 3 will compose this theorem with `exists_classified_senRightsWitness`;
this theorem intentionally accepts an already classified witness.
-/
theorem classifiedWitness_not_socialAcyclic
    (F : SWF Voter Alt)
    (hUN : UN F)
    (cw : ClassifiedSenRightsWitness F) :
    ¬ SocialAcyclic F :=
  (outcome_of_classifiedWitness F hUN cw).refutes_socialAcyclic

/-- Convenience corollary for O2. -/
theorem O2_refutes_socialAcyclic
    (F : SWF Voter Alt)
    (wit : SenRightsWitness F)
    (hz : wit.z ∈ ({wit.x, wit.y} : Finset Alt))
    (hw : wit.w ∈ ({wit.x, wit.y} : Finset Alt)) :
    ¬ SocialAcyclic F :=
  (outcome_of_twoOverlap F wit hz hw).refutes_socialAcyclic

/-- Convenience corollary for O3 z-only. -/
theorem O3_zOnly_refutes_socialAcyclic
    (F : SWF Voter Alt)
    (hUN : UN F)
    (wit : SenRightsWitness F)
    (hz : wit.z ∈ ({wit.x, wit.y} : Finset Alt))
    (hw : wit.w ∉ ({wit.x, wit.y} : Finset Alt)) :
    ¬ SocialAcyclic F :=
  (outcome_of_zOnly F hUN wit hz hw).refutes_socialAcyclic

/-- Convenience corollary for O3 w-only. -/
theorem O3_wOnly_refutes_socialAcyclic
    (F : SWF Voter Alt)
    (hUN : UN F)
    (wit : SenRightsWitness F)
    (hz : wit.z ∉ ({wit.x, wit.y} : Finset Alt))
    (hw : wit.w ∈ ({wit.x, wit.y} : Finset Alt)) :
    ¬ SocialAcyclic F :=
  (outcome_of_wOnly F hUN wit hz hw).refutes_socialAcyclic

/-- Convenience corollary for O4. -/
theorem O4_refutes_socialAcyclic
    (F : SWF Voter Alt)
    (hUN : UN F)
    (wit : SenRightsWitness F)
    (hz : wit.z ∉ ({wit.x, wit.y} : Finset Alt))
    (hw : wit.w ∉ ({wit.x, wit.y} : Finset Alt)) :
    ¬ SocialAcyclic F :=
  (outcome_of_disjoint F hUN wit hz hw).refutes_socialAcyclic

end SocialChoiceAtlas.Sen
