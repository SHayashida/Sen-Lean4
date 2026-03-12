/-
Copyright (c) 2025 SocialChoiceAtlas Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SocialChoiceAtlas Contributors
-/
import SocialChoiceAtlas.Core.Ranking

/-!
# Profiles and Social Welfare Functions

A profile assigns a ranking to each voter.
A social welfare function (SWF) maps profiles to social binary relations.
-/

namespace SocialChoiceAtlas

universe u v
variable (Voter : Type u) (Alt : Type v) [DecidableEq Alt] [Fintype Alt]

/-- A profile assigns to each voter a ranking over alternatives. -/
def Profile := Voter → Ranking Alt

/-- A social welfare function maps profiles to social preference relations.
    The output is a binary relation on alternatives (not necessarily an order). -/
def SWF := Profile Voter Alt → (Alt → Alt → Prop)

variable {Voter : Type u} {Alt : Type v} [DecidableEq Alt] [Fintype Alt]

/-- Helper: does voter i prefer x to y in profile p? -/
def prefers_i (p : Profile Voter Alt) (i : Voter) (x y : Alt) : Prop :=
  (p i).prefers x y

instance decidablePrefers_i [DecidableEq Voter] (p : Profile Voter Alt) (i : Voter) (x y : Alt) :
    Decidable (prefers_i p i x y) :=
  Ranking.decidablePrefers (p i) x y

end SocialChoiceAtlas
