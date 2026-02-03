/-
Copyright (c) 2025 SocialChoiceAtlas Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SocialChoiceAtlas Contributors
-/
import SocialChoiceAtlas.Core.Basics
import SocialChoiceAtlas.Axioms.Pareto
import SocialChoiceAtlas.Axioms.Liberalism
import SocialChoiceAtlas.Axioms.Rationality
import SocialChoiceAtlas.Sen.BaseCase24.Spec
import Mathlib.Tactic.FinCases

/-!
# Sen's Impossibility Theorem (Base Case: 2 Voters, 4 Alternatives)

This module states and proves Sen's "Impossibility of a Paretian Liberal"
for the fixed finite case of 2 voters and 4 alternatives.

## Main Results

- `sen_not_acyclic`: Under UN and MINLIB, there exists a profile where the social strict part is not acyclic.
- `sen_impossibility_basecase`: UN ∧ MINLIB → ¬SocialAcyclic (impossibility).

## Proof Strategy

The proof proceeds by case analysis on the decisive pairs. Given MINLIB,
we have voters i ≠ j with decisive pairs (x,y) and (z,w). We construct
a "witness profile" where the preferences create a cycle via the interplay
of unanimity and individual rights.

The key insight: when decisive pairs overlap appropriately, we can always
find preferences that create the cycle a P b P c P a in the social ordering.
-/

namespace SocialChoiceAtlas.Sen.BaseCase24

open SocialChoiceAtlas

/-! ### Auxiliary Constructions -/

/-- Build a ranking from a list (with proof obligations). -/
def mkRanking (l : List Alt) (hnodup : l.Nodup) (hcomplete : ∀ a : Alt, a ∈ l) :
    Ranking Alt :=
  ⟨l, hnodup, hcomplete⟩

/-- Standard ranking: 0 > 1 > 2 > 3 (descending by value). -/
def ranking0123 : Ranking Alt := mkRanking [0, 1, 2, 3]
  (by decide)
  (by intro a; fin_cases a <;> simp)

/-- Reversed ranking: 3 > 2 > 1 > 0. -/
def ranking3210 : Ranking Alt := mkRanking [3, 2, 1, 0]
  (by decide)
  (by intro a; fin_cases a <;> simp)

/-! ### Profiles and Concrete Rankings -/

/-- Build a two-voter profile from rankings for voters `0` and `1`. -/
def profile2 (r0 r1 : Ranking Alt) : Profile24 :=
  fun v => if v = (0 : Voter) then r0 else r1

@[simp] theorem profile2_apply_voter0 (r0 r1 : Ranking Alt) : profile2 r0 r1 voter0 = r0 := by
  simp [profile2, voter0]

@[simp] theorem profile2_apply_voter1 (r0 r1 : Ranking Alt) : profile2 r0 r1 voter1 = r1 := by
  simp [profile2, voter0, voter1]

@[simp] theorem prefers_i_profile2_voter0 (r0 r1 : Ranking Alt) (a b : Alt) :
    prefers_i (profile2 r0 r1) voter0 a b ↔ r0.prefers a b := by
  simp [prefers_i, profile2, voter0]

@[simp] theorem prefers_i_profile2_voter1 (r0 r1 : Ranking Alt) (a b : Alt) :
    prefers_i (profile2 r0 r1) voter1 a b ↔ r1.prefers a b := by
  simp [prefers_i, profile2, voter0, voter1]

section ListFacts

universe u
variable {β : Type u} [DecidableEq β]

lemma beq_false_of_ne (a b : β) (h : a ≠ b) : (a == b) = false := by
  cases hab : (a == b) with
  | true =>
      have : a = b := (beq_iff_eq).1 hab
      exact (h this).elim
  | false =>
      rfl

lemma beq_true (a : β) : (a == a) = true :=
  (beq_iff_eq).2 rfl

end ListFacts

/-- Build a ranking from four (distinct) alternatives; completeness is derived
from `Nodup` together with `Fintype.card Alt = 4`. -/
def mkRanking4 (a b c d : Alt) (hnodup : ([a, b, c, d] : List Alt).Nodup) : Ranking Alt :=
  mkRanking [a, b, c, d] hnodup (by
    classical
    have hCardList : ([a, b, c, d] : List Alt).toFinset.card = 4 := by
      simpa using (List.toFinset_card_of_nodup (l := ([a, b, c, d] : List Alt)) hnodup)
    have hCardAlt : Fintype.card Alt = 4 := by
      simp [Alt]
    have hUniv : ([a, b, c, d] : List Alt).toFinset = Finset.univ :=
      Finset.eq_univ_of_card _ (by simpa [hCardAlt] using hCardList)
    intro t
    have ht : t ∈ ([a, b, c, d] : List Alt).toFinset := by
      simpa [hUniv]
    exact (List.mem_toFinset).1 ht
  )

/-! ### Proof of Impossibility -/

section MainTheorem

variable (F : SWF24)

/--
Given MINLIB, extract the witness structure: two distinct voters with decisive pairs.
-/
structure MINLIBWitness where
  i : Voter
  j : Voter
  i_ne_j : i ≠ j
  x : Alt
  y : Alt
  x_ne_y : x ≠ y
  dec_i : Decisive F i x y
  z : Alt
  w : Alt
  z_ne_w : z ≠ w
  dec_j : Decisive F j z w

/-- Extract witness from MINLIB hypothesis. -/
noncomputable def extractWitness (hMINLIB : MINLIB F) : MINLIBWitness F := by
  classical
  have : ∃ w : MINLIBWitness F, True := by
    rcases hMINLIB with ⟨i, j, hij, x, y, z, w, hxy, hzw, hdeci, hdecj⟩
    exact ⟨⟨i, j, hij, x, y, hxy, hdeci, z, w, hzw, hdecj⟩, trivial⟩
  exact Classical.choose this

/-!
### Core Lemma: Constructing the Cycle

The proof strategy depends on whether the decisive pairs overlap.
We handle several cases:

**Case 1: Disjoint pairs** - pairs {x,y} and {z,w} are disjoint.
  We use all four alternatives to construct the cycle.

**Case 2: Overlapping pairs** - some alternatives coincide.
  Sub-cases require careful profile construction.

For the base case with 4 alternatives, we can always find a suitable
configuration. The full case analysis is non-trivial but finite.
-/

/--
Under UN and MINLIB, there exists a profile `p` such that the social strict part
`P (F p)` is not acyclic.

This follows the standard 3-case analysis (Endriss/Sen):
1. same decisive pair (immediate contradiction),
2. overlap in exactly one alternative (forces a 3-cycle),
3. disjoint pairs (forces a 4-cycle).
-/
private lemma sen_not_acyclic_01 (hUN : UN F)
    {x y z w : Alt} (hxy : x ≠ y) (hzw : z ≠ w)
    (hdec0 : Decisive F voter0 x y) (hdec1 : Decisive F voter1 z w) :
    ∃ p : Profile24, ¬Acyclic (strictPart (F p)) := by
  classical
  by_cases hz : z ∈ ({x, y} : Finset Alt)
  · by_cases hw : w ∈ ({x, y} : Finset Alt)
    · -- Case 1: {x,y} = {z,w} (two-point overlap) → contradiction.
      have hz' : z = x ∨ z = y := by simpa using hz
      have hw' : w = x ∨ w = y := by simpa using hw
      have hzw' : (z = x ∧ w = y) ∨ (z = y ∧ w = x) := by
        cases hz' with
        | inl hzx =>
          subst hzx
          cases hw' with
          | inl hwx =>
            cases (hzw (by simpa [hwx]))
          | inr hwy =>
            exact Or.inl ⟨rfl, hwy⟩
        | inr hzy =>
          subst hzy
          cases hw' with
          | inl hwx =>
            exact Or.inr ⟨rfl, hwx⟩
          | inr hwy =>
            cases (hzw (by simpa [hwy]))
      -- Choose the two remaining alternatives (other than x,y).
      let rem : Finset Alt := ((Finset.univ.erase x).erase y)
      have hy_mem : y ∈ (Finset.univ : Finset Alt).erase x := by
        simp [Finset.mem_erase, hxy.symm]
      have hCardRem : rem.card = 2 := by
        have : (((Finset.univ : Finset Alt).erase x).erase y).card =
            ((Finset.univ : Finset Alt).erase x).card - 1 :=
          Finset.card_erase_of_mem (s := (Finset.univ : Finset Alt).erase x) (a := y) hy_mem
        simpa [rem, Alt] using this
      have hRemNonempty : rem.Nonempty := (Finset.card_pos).1 (by simp [hCardRem])
      rcases hRemNonempty with ⟨t, ht⟩
      let rem' : Finset Alt := rem.erase t
      have hCardRem' : rem'.card = 1 := by
        have : (rem.erase t).card = rem.card - 1 :=
          Finset.card_erase_of_mem (s := rem) (a := t) ht
        simpa [rem', hCardRem] using this
      have hRem'Nonempty : rem'.Nonempty := (Finset.card_pos).1 (by simp [hCardRem'])
      rcases hRem'Nonempty with ⟨u, hu⟩
      have htu : t ≠ u := (Finset.mem_erase.1 hu).1.symm
      have ht_ne_y : t ≠ y := (Finset.mem_erase.1 ht).1
      have ht_mem : t ∈ (Finset.univ : Finset Alt).erase x := (Finset.mem_erase.1 ht).2
      have ht_ne_x : t ≠ x := (Finset.mem_erase.1 ht_mem).1
      have hu_mem : u ∈ rem := (Finset.mem_erase.1 hu).2
      have hu_ne_y : u ≠ y := (Finset.mem_erase.1 hu_mem).1
      have hu_mem' : u ∈ (Finset.univ : Finset Alt).erase x := (Finset.mem_erase.1 hu_mem).2
      have hu_ne_x : u ≠ x := (Finset.mem_erase.1 hu_mem').1
      -- Rankings: voter0 has x > y, voter1 has y > x.
      have hnodup_xy : ([x, y, t, u] : List Alt).Nodup := by
        simp [hxy, ht_ne_x, ht_ne_x.symm, ht_ne_y, ht_ne_y.symm,
          hu_ne_x, hu_ne_x.symm, hu_ne_y, hu_ne_y.symm, htu, htu.symm]
      have hnodup_yx : ([y, x, t, u] : List Alt).Nodup := by
        simp [hxy.symm, ht_ne_x, ht_ne_x.symm, ht_ne_y, ht_ne_y.symm,
          hu_ne_x, hu_ne_x.symm, hu_ne_y, hu_ne_y.symm, htu, htu.symm]
      let r0 : Ranking Alt := mkRanking4 x y t u hnodup_xy
      let r1 : Ranking Alt := mkRanking4 y x t u hnodup_yx
      let p : Profile24 := profile2 r0 r1
      have h0_xy : prefers_i p voter0 x y := by
        simp [Ranking.prefers, Ranking.position, p, r0, mkRanking4, mkRanking,
          List.indexOf_cons, beq_true, beq_false_of_ne, hxy]
      have h1_yx : prefers_i p voter1 y x := by
        simp [Ranking.prefers, Ranking.position, p, r1, mkRanking4, mkRanking,
          List.indexOf_cons, beq_true, beq_false_of_ne, hxy.symm]
      have hxPy : strictPart (F p) x y := (hdec0 p).1 h0_xy
      have hyPx : strictPart (F p) y x := by
        rcases hzw' with ⟨hzx, hwy⟩ | ⟨hzy, hwx⟩
        · subst hzx; subst hwy
          exact (hdec1 p).2 h1_yx
        · subst hzy; subst hwx
          exact (hdec1 p).1 h1_yx
      have : False := (strictPart_asymm (R := F p) x y hxPy) hyPx
      exact False.elim this
    · -- Case 2: z ∈ {x,y}, w ∉ {x,y} → 3-cycle.
      have hz' : z = x ∨ z = y := by simpa using hz
      have hwx : w ≠ x := by
        intro h
        apply hw
        simpa [h]
      have hwy : w ≠ y := by
        intro h
        apply hw
        simpa [h]
      cases hz' with
      | inl hzx =>
        -- Shared alternative is x. Build a 3-cycle: y P x, x P w, w P y.
        let rem : Finset Alt := (((Finset.univ.erase y).erase x).erase w)
        have hx_mem : x ∈ (Finset.univ : Finset Alt).erase y := by
          simp [Finset.mem_erase, hxy]
        have hw_mem : w ∈ ((Finset.univ : Finset Alt).erase y).erase x := by
          simp [Finset.mem_erase, hwx, hwy]
        have hCardRem : rem.card = 1 := by
          have h1 : (((Finset.univ : Finset Alt).erase y).erase x).card =
              ((Finset.univ : Finset Alt).erase y).card - 1 :=
            Finset.card_erase_of_mem (s := (Finset.univ : Finset Alt).erase y) (a := x) hx_mem
          have h2 : ((((Finset.univ : Finset Alt).erase y).erase x).erase w).card =
              (((Finset.univ : Finset Alt).erase y).erase x).card - 1 :=
            Finset.card_erase_of_mem (s := ((Finset.univ : Finset Alt).erase y).erase x) (a := w) hw_mem
          simpa [rem, Alt] using h2.trans (by simpa [Alt] using h1)
        have hRemNonempty : rem.Nonempty := (Finset.card_pos).1 (by simp [hCardRem])
        rcases hRemNonempty with ⟨t, ht⟩
        have ht_ne_w : t ≠ w := (Finset.mem_erase.1 ht).1
        have ht_mem1 : t ∈ ((Finset.univ : Finset Alt).erase y).erase x := (Finset.mem_erase.1 ht).2
        have ht_ne_x : t ≠ x := (Finset.mem_erase.1 ht_mem1).1
        have ht_mem2 : t ∈ (Finset.univ : Finset Alt).erase y := (Finset.mem_erase.1 ht_mem1).2
        have ht_ne_y : t ≠ y := (Finset.mem_erase.1 ht_mem2).1
        have hnodup0 : ([w, y, x, t] : List Alt).Nodup := by
          simp [hwy, hwx, hxy.symm, ht_ne_w.symm, ht_ne_y.symm, ht_ne_x.symm]
        have hnodup1 : ([x, w, y, t] : List Alt).Nodup := by
          simp [hwx.symm, hwy, hxy, ht_ne_x.symm, ht_ne_w.symm, ht_ne_y.symm]
        let r0 : Ranking Alt := mkRanking4 w y x t hnodup0
        let r1 : Ranking Alt := mkRanking4 x w y t hnodup1
        let p : Profile24 := profile2 r0 r1
        have h0_yx : prefers_i p voter0 y x := by
          simp [Ranking.prefers, Ranking.position, p, r0, mkRanking4, mkRanking,
            List.indexOf_cons, beq_true, beq_false_of_ne, hxy.symm, hwy, hwx]
        have h1_xw : prefers_i p voter1 x w := by
          simp [Ranking.prefers, Ranking.position, p, r1, mkRanking4, mkRanking,
            List.indexOf_cons, beq_true, beq_false_of_ne, hwx.symm]
        have hall_wy : ∀ v : Voter, prefers_i p v w y := by
          intro v
          fin_cases v <;> simp [Ranking.prefers, Ranking.position, p, r0, r1, mkRanking4, mkRanking,
            List.indexOf_cons, beq_true, beq_false_of_ne, hwy, hwy.symm, hwx, hwx.symm, hxy, hxy.symm,
            ht_ne_w, ht_ne_w.symm, ht_ne_x, ht_ne_x.symm, ht_ne_y, ht_ne_y.symm]
        have hyPx : strictPart (F p) y x := (hdec0 p).2 h0_yx
        have hxPw : strictPart (F p) x w := by
          simpa [hzx] using (hdec1 p).1 (by simpa [hzx] using h1_xw)
        have hwPy : strictPart (F p) w y := hUN p w y hall_wy
        have hcycle : cycle3 (strictPart (F p)) := by
          refine ⟨y, x, w, hxy.symm, hwx.symm, hwy, hyPx, hxPw, hwPy⟩
        exact ⟨p, cycle3_implies_not_acyclic hcycle⟩
      | inr hzy =>
        -- Shared alternative is y. Build a 3-cycle: x P y, y P w, w P x.
        let rem : Finset Alt := (((Finset.univ.erase x).erase y).erase w)
        have hy_mem : y ∈ (Finset.univ : Finset Alt).erase x := by
          simp [Finset.mem_erase, hxy.symm]
        have hw_mem : w ∈ ((Finset.univ : Finset Alt).erase x).erase y := by
          simp [Finset.mem_erase, hwx, hwy]
        have hCardRem : rem.card = 1 := by
          have h1 : (((Finset.univ : Finset Alt).erase x).erase y).card =
              ((Finset.univ : Finset Alt).erase x).card - 1 :=
            Finset.card_erase_of_mem (s := (Finset.univ : Finset Alt).erase x) (a := y) hy_mem
          have h2 : ((((Finset.univ : Finset Alt).erase x).erase y).erase w).card =
              (((Finset.univ : Finset Alt).erase x).erase y).card - 1 :=
            Finset.card_erase_of_mem (s := ((Finset.univ : Finset Alt).erase x).erase y) (a := w) hw_mem
          simpa [rem, Alt] using h2.trans (by simpa [Alt] using h1)
        have hRemNonempty : rem.Nonempty := (Finset.card_pos).1 (by simp [hCardRem])
        rcases hRemNonempty with ⟨t, ht⟩
        have ht_ne_w : t ≠ w := (Finset.mem_erase.1 ht).1
        have ht_mem1 : t ∈ ((Finset.univ : Finset Alt).erase x).erase y := (Finset.mem_erase.1 ht).2
        have ht_ne_y : t ≠ y := (Finset.mem_erase.1 ht_mem1).1
        have ht_mem2 : t ∈ (Finset.univ : Finset Alt).erase x := (Finset.mem_erase.1 ht_mem1).2
        have ht_ne_x : t ≠ x := (Finset.mem_erase.1 ht_mem2).1
        have hnodup0 : ([w, x, y, t] : List Alt).Nodup := by
          simp [hwx, hwy, hxy, ht_ne_w, ht_ne_w.symm, ht_ne_x, ht_ne_x.symm, ht_ne_y, ht_ne_y.symm]
        have hnodup1 : ([y, w, x, t] : List Alt).Nodup := by
          simp [hwy, hwy.symm, hwx, hwx.symm, hxy, hxy.symm, ht_ne_y, ht_ne_y.symm,
            ht_ne_w, ht_ne_w.symm, ht_ne_x, ht_ne_x.symm]
        let r0 : Ranking Alt := mkRanking4 w x y t hnodup0
        let r1 : Ranking Alt := mkRanking4 y w x t hnodup1
        let p : Profile24 := profile2 r0 r1
        have h0_xy : prefers_i p voter0 x y := by
          simp [Ranking.prefers, Ranking.position, p, r0, mkRanking4, mkRanking,
            List.indexOf_cons, beq_true, beq_false_of_ne, hwx, hwx.symm, hwy, hwy.symm, hxy, hxy.symm]
        have h1_yw : prefers_i p voter1 y w := by
          simp [Ranking.prefers, Ranking.position, p, r1, mkRanking4, mkRanking,
            List.indexOf_cons, beq_true, beq_false_of_ne, hwy, hwy.symm]
        have hall_wx : ∀ v : Voter, prefers_i p v w x := by
          intro v
          fin_cases v <;> simp [Ranking.prefers, Ranking.position, p, r0, r1, mkRanking4, mkRanking,
            List.indexOf_cons, beq_true, beq_false_of_ne, hwx, hwx.symm, hwy, hwy.symm, hxy, hxy.symm,
            ht_ne_w, ht_ne_w.symm, ht_ne_x, ht_ne_x.symm]
        have hxPy : strictPart (F p) x y := (hdec0 p).1 h0_xy
        have hyPw : strictPart (F p) y w := by
          simpa [hzy] using (hdec1 p).1 (by simpa [hzy] using h1_yw)
        have hwPx : strictPart (F p) w x := hUN p w x hall_wx
        have hcycle : cycle3 (strictPart (F p)) := by
          refine ⟨x, y, w, hxy, hwy.symm, hwx, hxPy, hyPw, hwPx⟩
        exact ⟨p, cycle3_implies_not_acyclic hcycle⟩
  · by_cases hw : w ∈ ({x, y} : Finset Alt)
    · -- Case 2: w ∈ {x,y}, z ∉ {x,y} → 3-cycle (using the second direction of decisiveness).
      have hw' : w = x ∨ w = y := by simpa using hw
      have hzx : z ≠ x := by
        intro h
        apply hz
        simpa [h]
      have hzy : z ≠ y := by
        intro h
        apply hz
        simpa [h]
      cases hw' with
      | inl hwx =>
        -- Shared alternative is x. Build a 3-cycle: y P x, x P z, z P y.
        let rem : Finset Alt := (((Finset.univ.erase y).erase x).erase z)
        have hx_mem : x ∈ (Finset.univ : Finset Alt).erase y := by
          simp [Finset.mem_erase, hxy]
        have hz_mem : z ∈ ((Finset.univ : Finset Alt).erase y).erase x := by
          simp [Finset.mem_erase, hzx, hzy]
        have hCardRem : rem.card = 1 := by
          have h1 : (((Finset.univ : Finset Alt).erase y).erase x).card =
              ((Finset.univ : Finset Alt).erase y).card - 1 :=
            Finset.card_erase_of_mem (s := (Finset.univ : Finset Alt).erase y) (a := x) hx_mem
          have h2 : ((((Finset.univ : Finset Alt).erase y).erase x).erase z).card =
              (((Finset.univ : Finset Alt).erase y).erase x).card - 1 :=
            Finset.card_erase_of_mem (s := ((Finset.univ : Finset Alt).erase y).erase x) (a := z) hz_mem
          simpa [rem, Alt] using h2.trans (by simpa [Alt] using h1)
        have hRemNonempty : rem.Nonempty := (Finset.card_pos).1 (by simp [hCardRem])
        rcases hRemNonempty with ⟨t, ht⟩
        have ht_ne_z : t ≠ z := (Finset.mem_erase.1 ht).1
        have ht_mem1 : t ∈ ((Finset.univ : Finset Alt).erase y).erase x := (Finset.mem_erase.1 ht).2
        have ht_ne_x : t ≠ x := (Finset.mem_erase.1 ht_mem1).1
        have ht_mem2 : t ∈ (Finset.univ : Finset Alt).erase y := (Finset.mem_erase.1 ht_mem1).2
        have ht_ne_y : t ≠ y := (Finset.mem_erase.1 ht_mem2).1
        have hnodup0 : ([z, y, x, t] : List Alt).Nodup := by
          simp [hzy, hzx, hxy.symm, ht_ne_z, ht_ne_z.symm, ht_ne_y, ht_ne_y.symm, ht_ne_x, ht_ne_x.symm]
        have hnodup1 : ([x, z, y, t] : List Alt).Nodup := by
          simp [hzx, hzx.symm, hzy, hzy.symm, hxy, hxy.symm,
            ht_ne_x, ht_ne_x.symm, ht_ne_z, ht_ne_z.symm, ht_ne_y, ht_ne_y.symm]
        let r0 : Ranking Alt := mkRanking4 z y x t hnodup0
        let r1 : Ranking Alt := mkRanking4 x z y t hnodup1
        let p : Profile24 := profile2 r0 r1
        have h0_yx : prefers_i p voter0 y x := by
          simp [Ranking.prefers, Ranking.position, p, r0, mkRanking4, mkRanking,
            List.indexOf_cons, beq_true, beq_false_of_ne, hzx, hzy, hxy.symm]
        have h1_xz : prefers_i p voter1 x z := by
          simp [Ranking.prefers, Ranking.position, p, r1, mkRanking4, mkRanking,
            List.indexOf_cons, beq_true, beq_false_of_ne, hzx.symm]
        have hall_zy : ∀ v : Voter, prefers_i p v z y := by
          intro v
          fin_cases v <;> simp [Ranking.prefers, Ranking.position, p, r0, r1, mkRanking4, mkRanking,
            List.indexOf_cons, beq_true, beq_false_of_ne, hzy, hzy.symm, hzx, hzx.symm, hxy, hxy.symm,
            ht_ne_z, ht_ne_z.symm, ht_ne_y, ht_ne_y.symm]
        have hyPx : strictPart (F p) y x := (hdec0 p).2 h0_yx
        have hxPz : strictPart (F p) x z := by
          simpa [hwx] using (hdec1 p).2 (by simpa [hwx] using h1_xz)
        have hzPy : strictPart (F p) z y := hUN p z y hall_zy
        have hcycle : cycle3 (strictPart (F p)) := by
          refine ⟨y, x, z, hxy.symm, hzx.symm, hzy, hyPx, hxPz, hzPy⟩
        exact ⟨p, cycle3_implies_not_acyclic hcycle⟩
      | inr hwy =>
        -- Shared alternative is y. Build a 3-cycle: x P y, y P z, z P x.
        let rem : Finset Alt := (((Finset.univ.erase x).erase y).erase z)
        have hy_mem : y ∈ (Finset.univ : Finset Alt).erase x := by
          simp [Finset.mem_erase, hxy.symm]
        have hz_mem : z ∈ ((Finset.univ : Finset Alt).erase x).erase y := by
          simp [Finset.mem_erase, hzx, hzy]
        have hCardRem : rem.card = 1 := by
          have h1 : (((Finset.univ : Finset Alt).erase x).erase y).card =
              ((Finset.univ : Finset Alt).erase x).card - 1 :=
            Finset.card_erase_of_mem (s := (Finset.univ : Finset Alt).erase x) (a := y) hy_mem
          have h2 : ((((Finset.univ : Finset Alt).erase x).erase y).erase z).card =
              (((Finset.univ : Finset Alt).erase x).erase y).card - 1 :=
            Finset.card_erase_of_mem (s := ((Finset.univ : Finset Alt).erase x).erase y) (a := z) hz_mem
          simpa [rem, Alt] using h2.trans (by simpa [Alt] using h1)
        have hRemNonempty : rem.Nonempty := (Finset.card_pos).1 (by simp [hCardRem])
        rcases hRemNonempty with ⟨t, ht⟩
        have ht_ne_z : t ≠ z := (Finset.mem_erase.1 ht).1
        have ht_mem1 : t ∈ ((Finset.univ : Finset Alt).erase x).erase y := (Finset.mem_erase.1 ht).2
        have ht_ne_y : t ≠ y := (Finset.mem_erase.1 ht_mem1).1
        have ht_mem2 : t ∈ (Finset.univ : Finset Alt).erase x := (Finset.mem_erase.1 ht_mem1).2
        have ht_ne_x : t ≠ x := (Finset.mem_erase.1 ht_mem2).1
        have hnodup0 : ([z, x, y, t] : List Alt).Nodup := by
          simp [hzx, hzy, hxy, ht_ne_z, ht_ne_z.symm, ht_ne_x, ht_ne_x.symm, ht_ne_y, ht_ne_y.symm]
        have hnodup1 : ([y, z, x, t] : List Alt).Nodup := by
          simp [hzy, hzy.symm, hzx, hzx.symm, hxy, hxy.symm,
            ht_ne_y, ht_ne_y.symm, ht_ne_z, ht_ne_z.symm, ht_ne_x, ht_ne_x.symm]
        let r0 : Ranking Alt := mkRanking4 z x y t hnodup0
        let r1 : Ranking Alt := mkRanking4 y z x t hnodup1
        let p : Profile24 := profile2 r0 r1
        have h0_xy : prefers_i p voter0 x y := by
          simp [Ranking.prefers, Ranking.position, p, r0, mkRanking4, mkRanking,
            List.indexOf_cons, beq_true, beq_false_of_ne, hzx, hzy, hxy, hxy.symm]
        have h1_yz : prefers_i p voter1 y z := by
          simp [Ranking.prefers, Ranking.position, p, r1, mkRanking4, mkRanking,
            List.indexOf_cons, beq_true, beq_false_of_ne, hzy.symm]
        have hall_zx : ∀ v : Voter, prefers_i p v z x := by
          intro v
          fin_cases v <;> simp [Ranking.prefers, Ranking.position, p, r0, r1, mkRanking4, mkRanking,
            List.indexOf_cons, beq_true, beq_false_of_ne, hzx, hzx.symm, hzy, hzy.symm, hxy, hxy.symm,
            ht_ne_z, ht_ne_z.symm, ht_ne_x, ht_ne_x.symm]
        have hxPy : strictPart (F p) x y := (hdec0 p).1 h0_xy
        have hyPz : strictPart (F p) y z := by
          simpa [hwy] using (hdec1 p).2 (by simpa [hwy] using h1_yz)
        have hzPx : strictPart (F p) z x := hUN p z x hall_zx
        have hcycle : cycle3 (strictPart (F p)) := by
          refine ⟨x, y, z, hxy, hzy.symm, hzx, hxPy, hyPz, hzPx⟩
        exact ⟨p, cycle3_implies_not_acyclic hcycle⟩
    · -- Case 3: {x,y} ∩ {z,w} = ∅ → 4-cycle.
      have hzx : z ≠ x := by
        intro h
        apply hz
        simpa [h]
      have hzy : z ≠ y := by
        intro h
        apply hz
        simpa [h]
      have hwx : w ≠ x := by
        intro h
        apply hw
        simpa [h]
      have hwy : w ≠ y := by
        intro h
        apply hw
        simpa [h]
      have hnodup0 : ([w, x, y, z] : List Alt).Nodup := by
        simp [hwx, hwy, hxy, hzx.symm, hzy.symm, hzw.symm]
      have hnodup1 : ([y, z, w, x] : List Alt).Nodup := by
        simp [hxy, hxy.symm, hzy, hzy.symm, hwx, hwx.symm, hzw, hwy, hwy.symm, hzx, hzx.symm]
      let r0 : Ranking Alt := mkRanking4 w x y z hnodup0
      let r1 : Ranking Alt := mkRanking4 y z w x hnodup1
      let p : Profile24 := profile2 r0 r1
      have h0_xy : prefers_i p voter0 x y := by
        simp [Ranking.prefers, Ranking.position, p, r0, mkRanking4, mkRanking,
          List.indexOf_cons, beq_true, beq_false_of_ne, hwx, hwx.symm, hwy, hwy.symm, hxy, hxy.symm]
      have h1_zw : prefers_i p voter1 z w := by
        simp [Ranking.prefers, Ranking.position, p, r1, mkRanking4, mkRanking,
          List.indexOf_cons, beq_true, beq_false_of_ne, hzw, hzw.symm, hzy, hzy.symm, hwy, hwy.symm,
            hzx, hzx.symm, hwx, hwx.symm]
      have hall_yz : ∀ v : Voter, prefers_i p v y z := by
        intro v
        fin_cases v <;> simp [Ranking.prefers, Ranking.position, p, r0, r1, mkRanking4, mkRanking,
          List.indexOf_cons, beq_true, beq_false_of_ne, hzy, hzy.symm, hxy, hxy.symm, hzx, hzx.symm,
            hwy, hwy.symm, hwx, hwx.symm, hzw, hzw.symm]
      have hall_wx : ∀ v : Voter, prefers_i p v w x := by
        intro v
        fin_cases v <;> simp [Ranking.prefers, Ranking.position, p, r0, r1, mkRanking4, mkRanking,
          List.indexOf_cons, beq_true, beq_false_of_ne, hwx, hwx.symm, hwy, hwy.symm, hzw, hzw.symm,
            hzx, hzx.symm, hxy, hxy.symm, hzy, hzy.symm]
      have hxPy : strictPart (F p) x y := (hdec0 p).1 h0_xy
      have hyPz : strictPart (F p) y z := hUN p y z hall_yz
      have hzPw : strictPart (F p) z w := (hdec1 p).1 h1_zw
      have hwPx : strictPart (F p) w x := hUN p w x hall_wx
      have hcycle : cycle4 (strictPart (F p)) := by
        refine ⟨x, y, z, w, hxy, hzy.symm, hzw, hwx, hxPy, hyPz, hzPw, hwPx⟩
      exact ⟨p, cycle4_implies_not_acyclic hcycle⟩

lemma sen_not_acyclic (hUN : UN F) (hMINLIB : MINLIB F) :
    ∃ p : Profile24, ¬Acyclic (strictPart (F p)) := by
  classical
  rcases hMINLIB with ⟨i, j, hij, x, y, z, w, hxy, hzw, hdeci, hdecj⟩
  fin_cases i <;> fin_cases j
  · cases hij rfl
  · exact sen_not_acyclic_01 (F := F) hUN (x := x) (y := y) (z := z) (w := w) hxy hzw hdeci hdecj
  · -- Swap roles so that voter0 is decisive on (z,w) and voter1 on (x,y).
    exact sen_not_acyclic_01 (F := F) hUN (x := z) (y := w) (z := x) (w := y) hzw hxy hdecj hdeci
  · cases hij rfl

/--
**Main Theorem**: Sen's Impossibility for the 2-voter, 4-alternative case.

No social welfare function can simultaneously satisfy:
- Unanimity (UN)
- Minimal Liberalism (MINLIB)
- Social Acyclicity
-/
theorem sen_impossibility_basecase (hUN : UN F) (hMINLIB : MINLIB F) :
    ¬SocialAcyclic F := by
  obtain ⟨p, hp⟩ := sen_not_acyclic F hUN hMINLIB
  intro hAcyclic
  exact hp (hAcyclic p)

end MainTheorem

end SocialChoiceAtlas.Sen.BaseCase24
