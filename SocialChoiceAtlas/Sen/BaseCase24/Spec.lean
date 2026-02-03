/-
Copyright (c) 2025 SocialChoiceAtlas Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SocialChoiceAtlas Contributors
-/
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic.FinCases
import SocialChoiceAtlas.Core.Profile

/-!
# Sen Base Case Specification: 2 Voters, 4 Alternatives

This module fixes the base case for Sen's impossibility theorem:
- 2 voters (Fin 2)
- 4 alternatives (Fin 4)

This finite, decidable setting enables SAT-based proof certificate verification.
-/

namespace SocialChoiceAtlas.Sen.BaseCase24

/-- Two voters: 0 and 1. -/
abbrev Voter := Fin 2

/-- Four alternatives: 0, 1, 2, 3. -/
abbrev Alt := Fin 4

-- Named voters for readability
abbrev voter0 : Voter := 0
abbrev voter1 : Voter := 1

-- Named alternatives for readability
abbrev alt0 : Alt := 0
abbrev alt1 : Alt := 1
abbrev alt2 : Alt := 2
abbrev alt3 : Alt := 3

-- Derive instances
instance : DecidableEq Voter := inferInstance
instance : DecidableEq Alt := inferInstance
instance : Fintype Voter := inferInstance
instance : Fintype Alt := inferInstance

/-- Profile type specialized to our base case. -/
abbrev Profile24 := Profile Voter Alt

/-- SWF type specialized to our base case. -/
abbrev SWF24 := SWF Voter Alt

/-- Helper to enumerate all voters. -/
def allVoters : List Voter := [0, 1]

/-- Helper to enumerate all alternatives. -/
def allAlts : List Alt := [0, 1, 2, 3]

theorem allVoters_complete : ∀ v : Voter, v ∈ allVoters := by
  intro v
  fin_cases v <;> simp [allVoters]

theorem allAlts_complete : ∀ a : Alt, a ∈ allAlts := by
  intro a
  fin_cases a <;> simp [allAlts]

end SocialChoiceAtlas.Sen.BaseCase24
