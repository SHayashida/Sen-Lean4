/-
Copyright (c) 2026 SocialChoiceAtlas Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SocialChoiceAtlas Contributors
-/
import Mathlib.Data.Finset.Card
import SocialChoiceAtlas.Core.Profile
import SocialChoiceAtlas.Axioms.Liberalism

/-!
# Sen Obstruction Basis, Stage 1

This module is Stage 1 of the M2 finite-obstruction bridge refactor.
It introduces a public semantic witness object for the data exposed by
`MINLIB`, together with an exhaustive finite overlap-shape classification.

Stage 1 deliberately does **not** modify `sen_impossibility_lifts`. It also
does not establish shape soundness, reconstruct the impossibility theorem,
transport the Sen24 CNF artifacts, define a literal two-voter restriction
theorem, or prove any repair/MCS transfer result.

The safe reading is:

> A general `MINLIB` instance exposes two distinguished rights holders and at
> most four distinguished alternatives.

The canonical labels `O2`, `O3`, and `O4` refer to the cardinality shape of the
two decisive-pair support after overlap classification. Their soundness as
strict-conflict / cycle-producing cases is reserved for a later stage.
-/

namespace SocialChoiceAtlas.Sen

open SocialChoiceAtlas

universe u v

variable {Voter : Type u} {Alt : Type v} [DecidableEq Alt] [Fintype Alt]

/--
Public package for the two rights holders and two decisive ordered pairs
exposed by `MINLIB`.

No pair-disjointness or all-distinctness assumption is included: the two
decisive pairs may overlap in zero, one, or two alternatives.
-/
structure SenRightsWitness (F : SWF Voter Alt) where
  i : Voter
  j : Voter
  i_ne_j : i ≠ j
  x : Alt
  y : Alt
  z : Alt
  w : Alt
  x_ne_y : x ≠ y
  z_ne_w : z ≠ w
  decisive_i : Decisive F i x y
  decisive_j : Decisive F j z w

namespace SenRightsWitness

/-- The distinguished alternative support carried by a Sen rights witness. -/
def support {F : SWF Voter Alt} (wit : SenRightsWitness F) : Finset Alt :=
  {wit.x, wit.y, wit.z, wit.w}

/-- Stage-1 bounded support: at most four distinguished alternatives. -/
theorem support_card_le_four {F : SWF Voter Alt} (wit : SenRightsWitness F) :
    wit.support.card ≤ 4 := by
  classical
  simpa [support] using
    (Finset.card_le_four (a := wit.x) (b := wit.y) (c := wit.z) (d := wit.w))

end SenRightsWitness

/--
Extract the public witness package from `MINLIB`.

This is intentionally just the public, reusable unpacking of the nested
existential in `MINLIB`; it does not use any impossibility theorem.
-/
theorem exists_senRightsWitness
    (F : SWF Voter Alt) (hMINLIB : MINLIB F) :
    Nonempty (SenRightsWitness F) := by
  rcases hMINLIB with ⟨i, j, hij, x, y, z, w, hxy, hzw, hdeci, hdecj⟩
  exact ⟨{
    i := i
    j := j
    i_ne_j := hij
    x := x
    y := y
    z := z
    w := w
    x_ne_y := hxy
    z_ne_w := hzw
    decisive_i := hdeci
    decisive_j := hdecj
  }⟩

/--
Raw four-way overlap shape matching the current M2 proof dispatcher:
membership of `z` and `w` in the first decisive pair support `{x, y}`.

Each constructor stores the branch conditions so later stages do not need to
repeat the same membership split.
-/
inductive SenRawOverlapShape (x y z w : Alt) : Type v where
  | twoOverlap
      (hz : z ∈ ({x, y} : Finset Alt))
      (hw : w ∈ ({x, y} : Finset Alt))
  | zOnly
      (hz : z ∈ ({x, y} : Finset Alt))
      (hw : w ∉ ({x, y} : Finset Alt))
  | wOnly
      (hz : z ∉ ({x, y} : Finset Alt))
      (hw : w ∈ ({x, y} : Finset Alt))
  | disjoint
      (hz : z ∉ ({x, y} : Finset Alt))
      (hw : w ∉ ({x, y} : Finset Alt))

/--
Paper-facing canonical support kind:

* `O2`: the two decisive pairs use the same two alternatives, up to orientation.
* `O3`: exactly one endpoint of the second pair lies in the first pair support.
* `O4`: the two decisive pair supports are disjoint.
-/
inductive SenObstructionShape where
  | O2
  | O3
  | O4
  deriving DecidableEq, Repr

namespace SenRawOverlapShape

/-- Canonical O2/O3/O4 support kind induced by a raw branch. -/
def kind {x y z w : Alt} :
    SenRawOverlapShape x y z w → SenObstructionShape
  | twoOverlap _ _ => SenObstructionShape.O2
  | zOnly _ _ => SenObstructionShape.O3
  | wOnly _ _ => SenObstructionShape.O3
  | disjoint _ _ => SenObstructionShape.O4

end SenRawOverlapShape

/-- Exhaustive raw overlap classification for any extracted Sen rights witness. -/
def classify_raw_overlap {F : SWF Voter Alt}
    (wit : SenRightsWitness F) :
    SenRawOverlapShape wit.x wit.y wit.z wit.w := by
  classical
  by_cases hz : wit.z ∈ ({wit.x, wit.y} : Finset Alt)
  · by_cases hw : wit.w ∈ ({wit.x, wit.y} : Finset Alt)
    · exact SenRawOverlapShape.twoOverlap hz hw
    · exact SenRawOverlapShape.zOnly hz hw
  · by_cases hw : wit.w ∈ ({wit.x, wit.y} : Finset Alt)
    · exact SenRawOverlapShape.wOnly hz hw
    · exact SenRawOverlapShape.disjoint hz hw

/-- A witness bundled with its raw overlap branch. -/
structure ClassifiedSenRightsWitness (F : SWF Voter Alt) where
  witness : SenRightsWitness F
  rawShape : SenRawOverlapShape witness.x witness.y witness.z witness.w

namespace ClassifiedSenRightsWitness

/-- The canonical O2/O3/O4 kind associated to a classified witness. -/
def kind {F : SWF Voter Alt} (cw : ClassifiedSenRightsWitness F) :
    SenObstructionShape :=
  cw.rawShape.kind

/-- The distinguished alternative support of a classified witness. -/
def support {F : SWF Voter Alt} (cw : ClassifiedSenRightsWitness F) : Finset Alt :=
  cw.witness.support

/-- Classified witnesses inherit the Stage-1 support bound. -/
theorem support_card_le_four {F : SWF Voter Alt} (cw : ClassifiedSenRightsWitness F) :
    cw.support.card ≤ 4 :=
  cw.witness.support_card_le_four

end ClassifiedSenRightsWitness

/-- Stage-1 flagship: `MINLIB` yields a classified bounded rights witness. -/
theorem exists_classified_senRightsWitness
    (F : SWF Voter Alt) (hMINLIB : MINLIB F) :
    Nonempty (ClassifiedSenRightsWitness F) := by
  rcases exists_senRightsWitness F hMINLIB with ⟨wit⟩
  exact ⟨{
    witness := wit
    rawShape := classify_raw_overlap wit
  }⟩

end SocialChoiceAtlas.Sen
