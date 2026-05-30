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

/-! ### H2 — `4 ≤ Fintype.card (Fin m)` from `4 ≤ m` -/

/--
If `4 ≤ m`, then `Fin m` has at least four elements. This is the immediate
consumer of the prompt's `hm : 4 ≤ m` hypothesis and turns it into the form
expected by `exists_not_mem_of_card_lt`.
-/
lemma four_le_card_fin {m : ℕ} (hm : 4 ≤ m) : 4 ≤ Fintype.card (Fin m) := by
  simpa using hm

/-! ### H3 — Ranking completion from a Nodup prefix

The base-case proof uses `mkRanking4` to package the four cycle alternatives
into a `Ranking (Fin 4)`. At the lift, the four (or three) cycle alternatives
live in `Fin m` with `4 ≤ m`, so the remaining `m - k` alternatives must be
appended to form a complete ranking. The list
`l ++ (Finset.univ \ l.toFinset).toList`
is the canonical extension: `Nodup` because the two pieces are individually
`Nodup` and disjoint by construction, complete because every element of `α`
either appears in `l` or in the sdiff complement.

Callers consume this via the positional lemmas (`_position_lt` and
`_prefers_of_indexOf_lt`) and never have to unfold `List.indexOf` for a
symbolic `m`.
-/

/-- Append the complement (as a list) of a `Nodup` prefix so the result is a
permutation of the ambient finite type. The use of `Finset.toList` (a
choice-based enumeration) forces `noncomputable`; we only use the resulting
ranking through the abstract positional API below, never by computation. -/
private noncomputable def extendList {α : Type*} [DecidableEq α] [Fintype α]
    (l : List α) : List α :=
  l ++ (Finset.univ \ l.toFinset).toList

private lemma extendList_nodup {α : Type*} [DecidableEq α] [Fintype α]
    (l : List α) (hnodup : l.Nodup) : (extendList l).Nodup := by
  classical
  refine List.Nodup.append hnodup (Finset.nodup_toList _) ?_
  intro a ha hb
  have ha' : a ∈ l.toFinset := List.mem_toFinset.mpr ha
  have hb' : a ∈ (Finset.univ \ l.toFinset : Finset α) := Finset.mem_toList.mp hb
  exact (Finset.mem_sdiff.mp hb').2 ha'

private lemma extendList_complete {α : Type*} [DecidableEq α] [Fintype α]
    (l : List α) : ∀ a : α, a ∈ extendList l := by
  classical
  intro a
  by_cases h : a ∈ l
  · exact List.mem_append_left _ h
  · refine List.mem_append_right _ ?_
    have ha : a ∈ (Finset.univ \ l.toFinset : Finset α) := by
      refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, ?_⟩
      intro hcontra
      exact h (List.mem_toFinset.mp hcontra)
    exact (Finset.mem_toList).mpr ha

/-- The ranking that begins with the prefix `l` (assumed `Nodup`) and
continues with the rest of the ambient finite type in some fixed
(noncomputable) order. -/
noncomputable def rankingOfPrefix {α : Type*} [DecidableEq α] [Fintype α]
    (l : List α) (hnodup : l.Nodup) : Ranking α :=
  { toList := extendList l
    nodup := extendList_nodup l hnodup
    complete := extendList_complete l }

private lemma rankingOfPrefix_toList {α : Type*} [DecidableEq α] [Fintype α]
    (l : List α) (hnodup : l.Nodup) :
    (rankingOfPrefix l hnodup).toList = extendList l := rfl

/-- Position of a prefix element in the constructed ranking equals its index
in the prefix list. -/
lemma rankingOfPrefix_position_of_mem_prefix
    {α : Type*} [DecidableEq α] [Fintype α]
    (l : List α) (hnodup : l.Nodup) {a : α} (ha : a ∈ l) :
    (rankingOfPrefix l hnodup).position a = l.indexOf a := by
  classical
  show (extendList l).indexOf a = l.indexOf a
  unfold extendList
  exact List.indexOf_append_of_mem ha

/-- If two elements occur in the prefix and the first occurs strictly
earlier, then the constructed ranking strictly prefers the first to the
second. -/
lemma rankingOfPrefix_prefers_of_indexOf_lt
    {α : Type*} [DecidableEq α] [Fintype α]
    (l : List α) (hnodup : l.Nodup) {a b : α}
    (ha : a ∈ l) (hb : b ∈ l) (hab : l.indexOf a < l.indexOf b) :
    (rankingOfPrefix l hnodup).prefers a b := by
  unfold Ranking.prefers
  rw [rankingOfPrefix_position_of_mem_prefix l hnodup ha,
      rankingOfPrefix_position_of_mem_prefix l hnodup hb]
  exact hab

/-- Positional version of `rankingOfPrefix_position_of_mem_prefix`: the
position of `l[k]` (under the constructed ranking) is exactly `k`. This is
the form most useful when proving `prefers` facts from explicit small
prefixes — it avoids any reasoning about `List.indexOf` on symbolic
elements. -/
lemma rankingOfPrefix_position_getElem
    {α : Type*} [DecidableEq α] [Fintype α]
    (l : List α) (hnodup : l.Nodup) (k : ℕ) (h : k < l.length) :
    (rankingOfPrefix l hnodup).position l[k] = k := by
  classical
  have hmem : l[k] ∈ l := List.getElem_mem h
  rw [rankingOfPrefix_position_of_mem_prefix l hnodup hmem]
  exact List.indexOf_getElem hnodup k h

/-- Convenience: `r.prefers l[i] l[j]` when `i < j` and the prefix `l` is
`Nodup`. The proof of `prefers` is just `i < j` after positions are computed
to `i` and `j`. -/
lemma rankingOfPrefix_prefers_getElem
    {α : Type*} [DecidableEq α] [Fintype α]
    (l : List α) (hnodup : l.Nodup)
    {i j : ℕ} (hi : i < l.length) (hj : j < l.length) (hij : i < j) :
    (rankingOfPrefix l hnodup).prefers l[i] l[j] := by
  unfold Ranking.prefers
  rw [rankingOfPrefix_position_getElem l hnodup i hi,
      rankingOfPrefix_position_getElem l hnodup j hj]
  exact hij

/-- Convenience constructor: a four-element ranking starting with `[a, b, c, d]`.
The fresh alternative `d` is provided by the caller; for the lift this is
supplied by `exists_not_mem_of_card_lt` (or, for the disjoint case, by the
second decisive pair itself). -/
noncomputable def ranking4Prefix {α : Type*} [DecidableEq α] [Fintype α]
    (a b c d : α) (h : ([a, b, c, d] : List α).Nodup) : Ranking α :=
  rankingOfPrefix [a, b, c, d] h

lemma ranking4Prefix_prefers_of_lt
    {α : Type*} [DecidableEq α] [Fintype α]
    {a b c d : α} (h : ([a, b, c, d] : List α).Nodup)
    {x y : α}
    (hx : x ∈ ([a, b, c, d] : List α)) (hy : y ∈ ([a, b, c, d] : List α))
    (hxy : ([a, b, c, d] : List α).indexOf x < ([a, b, c, d] : List α).indexOf y) :
    (ranking4Prefix a b c d h).prefers x y :=
  rankingOfPrefix_prefers_of_indexOf_lt _ h hx hy hxy

/-! ### H4 — Two-voter profile lift

`liftProfile i r_i r_j j` is the polymorphic generalisation of the base-case
`profile2`. Every voter `k ≠ j` (including `i`, since `i ≠ j` is the calling
convention) uses ranking `r_i`; voter `j` uses `r_j`. The point of choosing
`r_i` as the constant default is risk R3 (plan §5): "all `n` voters prefer
`a` to `b`" reduces to "both `r_i` and `r_j` prefer `a` to `b`", matching the
two-voter unanimity checks in the base case verbatim.
-/

/-- Two-voter profile lift: voter `j` gets ranking `r_j`, every other voter
(including the implicit "decisive voter" `i` whenever the caller respects
`i ≠ j`) gets ranking `r_i`. The decisive voter index `i` is *not* a
parameter — it is fixed by the calling pattern in the lift proofs via
`prefers_i_liftProfile_at_other` with `hkj := hij`. -/
def liftProfile {n : ℕ} {α : Type*} [DecidableEq α] [Fintype α]
    (r_i r_j : Ranking α) (j : Fin n) : Profile (Fin n) α :=
  fun k => if k = j then r_j else r_i

@[simp] lemma liftProfile_apply_j {n : ℕ} {α : Type*} [DecidableEq α] [Fintype α]
    (r_i r_j : Ranking α) (j : Fin n) :
    liftProfile (n := n) (α := α) r_i r_j j j = r_j := by
  simp [liftProfile]

lemma liftProfile_apply_ne {n : ℕ} {α : Type*} [DecidableEq α] [Fintype α]
    (r_i r_j : Ranking α) {j k : Fin n} (hkj : k ≠ j) :
    liftProfile (n := n) (α := α) r_i r_j j k = r_i := by
  simp [liftProfile, hkj]

lemma prefers_i_liftProfile_at_j {n : ℕ} {α : Type*} [DecidableEq α] [Fintype α]
    (r_i r_j : Ranking α) (j : Fin n) (a b : α) :
    prefers_i (liftProfile (n := n) (α := α) r_i r_j j) j a b ↔ r_j.prefers a b := by
  unfold prefers_i
  simp [liftProfile]

lemma prefers_i_liftProfile_at_other {n : ℕ} {α : Type*} [DecidableEq α] [Fintype α]
    (r_i r_j : Ranking α) {j k : Fin n} (hkj : k ≠ j) (a b : α) :
    prefers_i (liftProfile (n := n) (α := α) r_i r_j j) k a b ↔ r_i.prefers a b := by
  unfold prefers_i
  simp [liftProfile, hkj]

lemma prefers_i_liftProfile_at_i {n : ℕ} {α : Type*} [DecidableEq α] [Fintype α]
    {i j : Fin n} (hij : i ≠ j) (r_i r_j : Ranking α) (a b : α) :
    prefers_i (liftProfile (n := n) (α := α) r_i r_j j) i a b ↔ r_i.prefers a b :=
  prefers_i_liftProfile_at_other (r_i := r_i) (r_j := r_j) (j := j) (k := i) hij a b

/-- Unanimity over all `n` voters in a `liftProfile` reduces to two-voter
agreement: `r_i.prefers a b` and `r_j.prefers a b`. This is the lift-side
analogue of the base case's `fin_cases v` enumeration over `Fin 2`. -/
lemma liftProfile_unanimous
    {n : ℕ} {α : Type*} [DecidableEq α] [Fintype α]
    (r_i r_j : Ranking α) (j : Fin n) {a b : α}
    (hi : r_i.prefers a b) (hj : r_j.prefers a b) :
    ∀ k : Fin n, prefers_i (liftProfile (n := n) (α := α) r_i r_j j) k a b := by
  intro k
  by_cases hkj : k = j
  · subst hkj
    exact (prefers_i_liftProfile_at_j r_i r_j k a b).mpr hj
  · exact (prefers_i_liftProfile_at_other r_i r_j hkj a b).mpr hi

/-! ### H5 — Sen lift: 3-case overlap analysis (polymorphic port)

Each case mirrors the corresponding branch of the base-case
`sen_not_acyclic_01`. The cycle pattern, the routing of decisive vs.
unanimity edges, and the role of `Decisive.symm` are unchanged; only the
ranking and profile constructions are generalised via H3/H4. -/

/-! ### H5 — Sen lift: 3-case overlap analysis (polymorphic port)

Each case mirrors the corresponding branch of the base-case
`sen_not_acyclic_01`. The cycle pattern, the routing of decisive vs.
unanimity edges, and the role of `Decisive.symm` are unchanged; only the
ranking and profile constructions are generalised via H3/H4.

Proof strategy for each case:
1. Pick concrete prefix lists for `r_i` and `r_j` so that the cycle
   vertices appear in the order needed.
2. Use `rankingOfPrefix_prefers_getElem` to read off `r.prefers a b` directly
   from the prefix's positional structure (no symbolic `List.indexOf`
   reduction is required).
3. Combine via `liftProfile_unanimous` (UN) and the supplied `Decisive`
   pairs (potentially through `Decisive.symm`).
-/

private lemma sen_lift_case_two_overlap
    {n m : ℕ} (F : SWF (Fin n) (Fin m))
    {i j : Fin n} (hij : i ≠ j)
    {x y z w : Fin m}
    (hxy : x ≠ y) (_hzw : z ≠ w)
    (hdec_i : Decisive F i x y) (hdec_j : Decisive F j z w)
    (hzw_eq : (z = x ∧ w = y) ∨ (z = y ∧ w = x)) :
    ¬ SocialAcyclic F := by
  classical
  have hnodup_xy : ([x, y] : List (Fin m)).Nodup := by simp [hxy]
  have hnodup_yx : ([y, x] : List (Fin m)).Nodup := by simp [hxy.symm]
  let r_i : Ranking (Fin m) := rankingOfPrefix [x, y] hnodup_xy
  let r_j : Ranking (Fin m) := rankingOfPrefix [y, x] hnodup_yx
  let p : Profile (Fin n) (Fin m) := liftProfile r_i r_j j
  -- r_i prefers x to y (positions 0 < 1 in [x, y]).
  have hri_xy : r_i.prefers x y :=
    rankingOfPrefix_prefers_getElem (l := [x, y]) hnodup_xy
      (i := 0) (j := 1) (by simp) (by simp) (by decide)
  have h_i_xy : prefers_i p i x y :=
    (prefers_i_liftProfile_at_i hij r_i r_j x y).mpr hri_xy
  -- r_j prefers y to x (positions 0 < 1 in [y, x]).
  have hrj_yx : r_j.prefers y x :=
    rankingOfPrefix_prefers_getElem (l := [y, x]) hnodup_yx
      (i := 0) (j := 1) (by simp) (by simp) (by decide)
  have h_j_yx : prefers_i p j y x :=
    (prefers_i_liftProfile_at_j r_i r_j j y x).mpr hrj_yx
  -- Voter i and voter j force opposite social strict preferences on (x, y).
  have hxPy : strictPart (F p) x y := (hdec_i p).1 h_i_xy
  have hyPx : strictPart (F p) y x := by
    rcases hzw_eq with ⟨hzx, hwy⟩ | ⟨hzy, hwx⟩
    · subst hzx; subst hwy
      exact (hdec_j p).2 h_j_yx
    · subst hzy; subst hwx
      exact (hdec_j p).1 h_j_yx
  intro _hAcyclic
  exact strictPart_asymm (R := F p) x y hxPy hyPx

/-- One-overlap subcase, shared alternative `x`, decisive pair for voter `j`
is `(x, w)` (with `w ∉ {x, y}`). Cycle constructed: `y P x P w P y`. -/
private lemma sen_lift_case_one_overlap_shared_x
    {n m : ℕ} (F : SWF (Fin n) (Fin m))
    (hUN : UN F) {i j : Fin n} (hij : i ≠ j)
    {x y w : Fin m}
    (hxy : x ≠ y) (hxw : x ≠ w)
    (hdec_i : Decisive F i x y) (hdec_j : Decisive F j x w)
    (hwy : w ≠ y) :
    ¬ SocialAcyclic F := by
  classical
  have hwx : w ≠ x := Ne.symm hxw
  have hnodup0 : ([w, y, x] : List (Fin m)).Nodup := by simp [hwy, hwx, hxy.symm]
  have hnodup1 : ([x, w, y] : List (Fin m)).Nodup := by simp [hxw, hxy, hwy]
  let r_i : Ranking (Fin m) := rankingOfPrefix [w, y, x] hnodup0
  let r_j : Ranking (Fin m) := rankingOfPrefix [x, w, y] hnodup1
  let p : Profile (Fin n) (Fin m) := liftProfile r_i r_j j
  -- r_i prefers y to x: positions 1 < 2 in [w, y, x].
  have hri_yx : r_i.prefers y x :=
    rankingOfPrefix_prefers_getElem (l := [w, y, x]) hnodup0
      (i := 1) (j := 2) (by simp) (by simp) (by decide)
  have h_i_yx : prefers_i p i y x :=
    (prefers_i_liftProfile_at_i hij r_i r_j y x).mpr hri_yx
  -- r_j prefers x to w: positions 0 < 1 in [x, w, y].
  have hrj_xw : r_j.prefers x w :=
    rankingOfPrefix_prefers_getElem (l := [x, w, y]) hnodup1
      (i := 0) (j := 1) (by simp) (by simp) (by decide)
  have h_j_xw : prefers_i p j x w :=
    (prefers_i_liftProfile_at_j r_i r_j j x w).mpr hrj_xw
  -- r_i prefers w to y: positions 0 < 1 in [w, y, x].
  have hri_wy : r_i.prefers w y :=
    rankingOfPrefix_prefers_getElem (l := [w, y, x]) hnodup0
      (i := 0) (j := 1) (by simp) (by simp) (by decide)
  -- r_j prefers w to y: positions 1 < 2 in [x, w, y].
  have hrj_wy : r_j.prefers w y :=
    rankingOfPrefix_prefers_getElem (l := [x, w, y]) hnodup1
      (i := 1) (j := 2) (by simp) (by simp) (by decide)
  have hall_wy : ∀ k : Fin n, prefers_i p k w y :=
    liftProfile_unanimous r_i r_j j hri_wy hrj_wy
  have hyPx : strictPart (F p) y x := (hdec_i p).2 h_i_yx
  have hxPw : strictPart (F p) x w := (hdec_j p).1 h_j_xw
  have hwPy : strictPart (F p) w y := hUN p w y hall_wy
  have hcycle : cycle3 (strictPart (F p)) :=
    ⟨y, x, w, hxy.symm, hwx.symm, hwy, hyPx, hxPw, hwPy⟩
  intro hAcyclic
  exact (cycle3_implies_not_acyclic hcycle) (hAcyclic p)

/-- One-overlap subcase, shared alternative `y`, decisive pair for voter `j`
is `(y, w)` (with `w ∉ {x, y}`). Cycle constructed: `x P y P w P x`. -/
private lemma sen_lift_case_one_overlap_shared_y
    {n m : ℕ} (F : SWF (Fin n) (Fin m))
    (hUN : UN F) {i j : Fin n} (hij : i ≠ j)
    {x y w : Fin m}
    (hxy : x ≠ y) (hyw : y ≠ w)
    (hdec_i : Decisive F i x y) (hdec_j : Decisive F j y w)
    (hwx : w ≠ x) :
    ¬ SocialAcyclic F := by
  classical
  have hwy : w ≠ y := Ne.symm hyw
  have hnodup0 : ([w, x, y] : List (Fin m)).Nodup := by simp [hwx, hwy, hxy]
  have hnodup1 : ([y, w, x] : List (Fin m)).Nodup := by simp [hyw, hxy.symm, hwx]
  let r_i : Ranking (Fin m) := rankingOfPrefix [w, x, y] hnodup0
  let r_j : Ranking (Fin m) := rankingOfPrefix [y, w, x] hnodup1
  let p : Profile (Fin n) (Fin m) := liftProfile r_i r_j j
  -- r_i prefers x to y: positions 1 < 2 in [w, x, y].
  have hri_xy : r_i.prefers x y :=
    rankingOfPrefix_prefers_getElem (l := [w, x, y]) hnodup0
      (i := 1) (j := 2) (by simp) (by simp) (by decide)
  have h_i_xy : prefers_i p i x y :=
    (prefers_i_liftProfile_at_i hij r_i r_j x y).mpr hri_xy
  -- r_j prefers y to w: positions 0 < 1 in [y, w, x].
  have hrj_yw : r_j.prefers y w :=
    rankingOfPrefix_prefers_getElem (l := [y, w, x]) hnodup1
      (i := 0) (j := 1) (by simp) (by simp) (by decide)
  have h_j_yw : prefers_i p j y w :=
    (prefers_i_liftProfile_at_j r_i r_j j y w).mpr hrj_yw
  -- r_i prefers w to x: positions 0 < 1 in [w, x, y].
  have hri_wx : r_i.prefers w x :=
    rankingOfPrefix_prefers_getElem (l := [w, x, y]) hnodup0
      (i := 0) (j := 1) (by simp) (by simp) (by decide)
  -- r_j prefers w to x: positions 1 < 2 in [y, w, x].
  have hrj_wx : r_j.prefers w x :=
    rankingOfPrefix_prefers_getElem (l := [y, w, x]) hnodup1
      (i := 1) (j := 2) (by simp) (by simp) (by decide)
  have hall_wx : ∀ k : Fin n, prefers_i p k w x :=
    liftProfile_unanimous r_i r_j j hri_wx hrj_wx
  have hxPy : strictPart (F p) x y := (hdec_i p).1 h_i_xy
  have hyPw : strictPart (F p) y w := (hdec_j p).1 h_j_yw
  have hwPx : strictPart (F p) w x := hUN p w x hall_wx
  have hcycle : cycle3 (strictPart (F p)) :=
    ⟨x, y, w, hxy, hwy.symm, hwx, hxPy, hyPw, hwPx⟩
  intro hAcyclic
  exact (cycle3_implies_not_acyclic hcycle) (hAcyclic p)

/-- One-overlap dispatcher: `z ∈ {x, y}` but `w ∉ {x, y}`. -/
private lemma sen_lift_case_one_overlap_z_in
    {n m : ℕ} (F : SWF (Fin n) (Fin m))
    (hUN : UN F) {i j : Fin n} (hij : i ≠ j)
    {x y z w : Fin m}
    (hxy : x ≠ y) (_hzw : z ≠ w)
    (hdec_i : Decisive F i x y) (hdec_j : Decisive F j z w)
    (hz : z ∈ ({x, y} : Finset (Fin m))) (hw_not : w ∉ ({x, y} : Finset (Fin m))) :
    ¬ SocialAcyclic F := by
  classical
  have hz' : z = x ∨ z = y := by simpa using hz
  have hwx : w ≠ x := by intro h; apply hw_not; simp [h]
  have hwy : w ≠ y := by intro h; apply hw_not; simp [h]
  cases hz' with
  | inl hzx =>
      have hdec_j' : Decisive F j x w := hzx ▸ hdec_j
      have hxw : x ≠ w := by intro h; exact hwx h.symm
      exact sen_lift_case_one_overlap_shared_x F hUN hij hxy hxw hdec_i hdec_j' hwy
  | inr hzy =>
      have hdec_j' : Decisive F j y w := hzy ▸ hdec_j
      have hyw : y ≠ w := by intro h; exact hwy h.symm
      exact sen_lift_case_one_overlap_shared_y F hUN hij hxy hyw hdec_i hdec_j' hwx

/-- One-overlap dispatcher: `w ∈ {x, y}` but `z ∉ {x, y}` — uses
`Decisive.symm` to swap the orientation of voter `j`'s decisive pair. -/
private lemma sen_lift_case_one_overlap_w_in
    {n m : ℕ} (F : SWF (Fin n) (Fin m))
    (hUN : UN F) {i j : Fin n} (hij : i ≠ j)
    {x y z w : Fin m}
    (hxy : x ≠ y) (hzw : z ≠ w)
    (hdec_i : Decisive F i x y) (hdec_j : Decisive F j z w)
    (hw : w ∈ ({x, y} : Finset (Fin m))) (hz_not : z ∉ ({x, y} : Finset (Fin m))) :
    ¬ SocialAcyclic F := by
  classical
  have hdec_j' : Decisive F j w z := hdec_j.symm
  exact sen_lift_case_one_overlap_z_in (F := F) (hUN := hUN) (hij := hij)
    (x := x) (y := y) (z := w) (w := z)
    (hxy := hxy) (_hzw := (Ne.symm hzw)) (hdec_i := hdec_i) (hdec_j := hdec_j')
    (hz := hw) (hw_not := hz_not)

/-- Disjoint case: `{x, y} ∩ {z, w} = ∅`. Cycle constructed:
`x P y P z P w P x`. -/
private lemma sen_lift_case_disjoint
    {n m : ℕ} (F : SWF (Fin n) (Fin m))
    (hUN : UN F) {i j : Fin n} (hij : i ≠ j)
    {x y z w : Fin m}
    (hxy : x ≠ y) (hzw : z ≠ w)
    (hdec_i : Decisive F i x y) (hdec_j : Decisive F j z w)
    (hzx : z ≠ x) (hzy : z ≠ y) (hwx : w ≠ x) (hwy : w ≠ y) :
    ¬ SocialAcyclic F := by
  classical
  have hnodup0 : ([w, x, y, z] : List (Fin m)).Nodup := by
    simp [hwx, hwy, hxy, hzx.symm, hzy.symm, hzw.symm]
  have hnodup1 : ([y, z, w, x] : List (Fin m)).Nodup := by
    simp [hxy, hxy.symm, hzy, hzy.symm, hwx, hwx.symm, hzw, hwy, hwy.symm, hzx, hzx.symm]
  let r_i : Ranking (Fin m) := rankingOfPrefix [w, x, y, z] hnodup0
  let r_j : Ranking (Fin m) := rankingOfPrefix [y, z, w, x] hnodup1
  let p : Profile (Fin n) (Fin m) := liftProfile r_i r_j j
  -- r_i prefers x to y: positions 1 < 2 in [w, x, y, z].
  have hri_xy : r_i.prefers x y :=
    rankingOfPrefix_prefers_getElem (l := [w, x, y, z]) hnodup0
      (i := 1) (j := 2) (by simp) (by simp) (by decide)
  have h_i_xy : prefers_i p i x y :=
    (prefers_i_liftProfile_at_i hij r_i r_j x y).mpr hri_xy
  -- r_j prefers z to w: positions 1 < 2 in [y, z, w, x].
  have hrj_zw : r_j.prefers z w :=
    rankingOfPrefix_prefers_getElem (l := [y, z, w, x]) hnodup1
      (i := 1) (j := 2) (by simp) (by simp) (by decide)
  have h_j_zw : prefers_i p j z w :=
    (prefers_i_liftProfile_at_j r_i r_j j z w).mpr hrj_zw
  -- r_i prefers y to z: positions 2 < 3 in [w, x, y, z].
  have hri_yz : r_i.prefers y z :=
    rankingOfPrefix_prefers_getElem (l := [w, x, y, z]) hnodup0
      (i := 2) (j := 3) (by simp) (by simp) (by decide)
  -- r_j prefers y to z: positions 0 < 1 in [y, z, w, x].
  have hrj_yz : r_j.prefers y z :=
    rankingOfPrefix_prefers_getElem (l := [y, z, w, x]) hnodup1
      (i := 0) (j := 1) (by simp) (by simp) (by decide)
  have hall_yz : ∀ k : Fin n, prefers_i p k y z :=
    liftProfile_unanimous r_i r_j j hri_yz hrj_yz
  -- r_i prefers w to x: positions 0 < 1 in [w, x, y, z].
  have hri_wx : r_i.prefers w x :=
    rankingOfPrefix_prefers_getElem (l := [w, x, y, z]) hnodup0
      (i := 0) (j := 1) (by simp) (by simp) (by decide)
  -- r_j prefers w to x: positions 2 < 3 in [y, z, w, x].
  have hrj_wx : r_j.prefers w x :=
    rankingOfPrefix_prefers_getElem (l := [y, z, w, x]) hnodup1
      (i := 2) (j := 3) (by simp) (by simp) (by decide)
  have hall_wx : ∀ k : Fin n, prefers_i p k w x :=
    liftProfile_unanimous r_i r_j j hri_wx hrj_wx
  have hxPy : strictPart (F p) x y := (hdec_i p).1 h_i_xy
  have hyPz : strictPart (F p) y z := hUN p y z hall_yz
  have hzPw : strictPart (F p) z w := (hdec_j p).1 h_j_zw
  have hwPx : strictPart (F p) w x := hUN p w x hall_wx
  have hcycle : cycle4 (strictPart (F p)) :=
    ⟨x, y, z, w, hxy, hzy.symm, hzw, hwx, hxPy, hyPz, hzPw, hwPx⟩
  intro hAcyclic
  exact (cycle4_implies_not_acyclic hcycle) (hAcyclic p)

/-! ### H6 — Main theorem: Sen's impossibility lifts -/

/--
**Sen's Impossibility Theorem — Lifted to `(Fin n, Fin m)` with `2 ≤ n`,
`4 ≤ m`.**

No social welfare function on `n` voters and `m` alternatives can
simultaneously satisfy weak Pareto / unanimity (`UN`) and minimal liberalism
(`MINLIB`) while keeping the social strict preference acyclic for every
profile (`SocialAcyclic`).

This is the M2 positive-bridge deliverable in the Lean Proof layer. The
statement reaches `SocialAcyclic` directly (no `no_cycle3/no_cycle4`
short-cycle restriction). For the relationship to the M1.5 CNF Witness/Audit
layer, see `docs/m2_scope_wall.md`.

The hypothesis `hn : 2 ≤ n` is logically redundant — `MINLIB` already
supplies two distinct voters in `Fin n`, so `Fin n` is automatically of
cardinality at least two — but is kept for statement symmetry with Sen's
original formulation. Similarly, `hm : 4 ≤ m` is implied by the existence
of two `Decisive` pairs over `Fin m` in the disjoint case; the explicit
hypothesis matches the prompt's signature and documents the lift scope.
-/
theorem sen_impossibility_lifts
    {n m : ℕ} (_hn : 2 ≤ n) (_hm : 4 ≤ m)
    (F : SWF (Fin n) (Fin m))
    (hUN : UN F) (hMINLIB : MINLIB F) :
    ¬ SocialAcyclic F := by
  classical
  rcases hMINLIB with ⟨i, j, hij, x, y, z, w, hxy, hzw, hdec_i, hdec_j⟩
  by_cases hz : z ∈ ({x, y} : Finset (Fin m))
  · by_cases hw : w ∈ ({x, y} : Finset (Fin m))
    · -- Two-overlap: {z, w} ⊆ {x, y}, combined with z ≠ w gives the equality.
      have hz' : z = x ∨ z = y := by simpa using hz
      have hw' : w = x ∨ w = y := by simpa using hw
      have hzw_eq : (z = x ∧ w = y) ∨ (z = y ∧ w = x) := by
        rcases hz' with hzx | hzy
        · rcases hw' with hwx | hwy
          · exact absurd (hzx.trans hwx.symm) hzw
          · exact Or.inl ⟨hzx, hwy⟩
        · rcases hw' with hwx | hwy
          · exact Or.inr ⟨hzy, hwx⟩
          · exact absurd (hzy.trans hwy.symm) hzw
      exact sen_lift_case_two_overlap F hij hxy hzw hdec_i hdec_j hzw_eq
    · -- One-overlap, z ∈ {x,y}, w ∉ {x,y}.
      exact sen_lift_case_one_overlap_z_in F hUN hij hxy hzw hdec_i hdec_j hz hw
  · by_cases hw : w ∈ ({x, y} : Finset (Fin m))
    · -- One-overlap, w ∈ {x,y}, z ∉ {x,y}.
      exact sen_lift_case_one_overlap_w_in F hUN hij hxy hzw hdec_i hdec_j hw hz
    · -- Disjoint case.
      have hzx : z ≠ x := by intro h; apply hz; simp [h]
      have hzy : z ≠ y := by intro h; apply hz; simp [h]
      have hwx : w ≠ x := by intro h; apply hw; simp [h]
      have hwy : w ≠ y := by intro h; apply hw; simp [h]
      exact sen_lift_case_disjoint F hUN hij hxy hzw hdec_i hdec_j hzx hzy hwx hwy

end SocialChoiceAtlas.Sen.Lifting
