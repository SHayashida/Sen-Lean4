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

- `sen_cycle3`: Under UN and MINLIB, there exists a profile inducing a 3-cycle.
- `sen_impossibility_basecase`: UN ∧ MINLIB → ¬SocialAcyclic.

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
    rcases hMINLIB with ⟨i, j, hij, x, y, hxy, hdeci, z, w, hzw, hdecj⟩
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

-- TODO: The full constructive proof requires extensive case analysis.
-- Below we provide the theorem statement and proof skeleton.
-- The `sorry` can be eliminated by:
-- 1. Explicit case split on pair configurations
-- 2. For each case, construct a witness profile
-- 3. Show the profile induces a 3-cycle
-- Alternatively, use SAT-based verification (see SAT.lean)

/--
**Key Lemma**: Under UN and MINLIB, we can construct a profile that
induces a 3-cycle in the social strict preference.
-/
lemma sen_cycle3 (hUN : UN F) (hMINLIB : MINLIB F) :
    ∃ p : Profile24, cycle3 (strictPart (F p)) := by
  -- Extract the MINLIB witness
  obtain ⟨i, j, hij, x, y, hxy, hdeci, z, w, hzw, hdecj⟩ := hMINLIB
  -- The proof proceeds by case analysis on whether {x,y} and {z,w} overlap
  -- and their relative positions.
  --
  -- Key insight: With 2 voters and 4 alternatives, we can always arrange
  -- preferences so that:
  -- - Voter i's decisiveness forces some P-relation
  -- - Voter j's decisiveness forces another P-relation
  -- - Unanimity forces a third P-relation
  -- - These three form a cycle
  --
  -- The detailed case analysis is marked as TODO for explicit construction
  -- or SAT-certificate verification.
  sorry

/--
**Main Theorem**: Sen's Impossibility for the 2-voter, 4-alternative case.

No social welfare function can simultaneously satisfy:
- Unanimity (UN)
- Minimal Liberalism (MINLIB)
- Social Acyclicity
-/
theorem sen_impossibility_basecase (hUN : UN F) (hMINLIB : MINLIB F) :
    ¬SocialAcyclic F := by
  -- Get a profile with a 3-cycle
  obtain ⟨p, hcycle⟩ := sen_cycle3 F hUN hMINLIB
  -- Use the acyclicity definition
  intro hAcyclic
  -- SocialAcyclic says ∀ p, Acyclic (strictPart (F p))
  have hAcyclicP := hAcyclic p
  -- But cycle3 implies ¬Acyclic
  exact cycle3_implies_not_acyclic hcycle hAcyclicP

end MainTheorem

/-! ### TODO Checklist for Completing the Proof

1. [ ] Case split in `sen_cycle3`:
   - Case A: {x,y} ∩ {z,w} = ∅ (disjoint pairs)
   - Case B: |{x,y} ∩ {z,w}| = 1 (one common element)
   - Case C: {x,y} = {z,w} (same pair, but i ≠ j)

2. [ ] For each case, define the witness profile explicitly:
   - Construct `Ranking Alt` for voter 0
   - Construct `Ranking Alt` for voter 1
   - Define profile as function mapping voters to rankings

3. [ ] Prove the cycle exists:
   - Identify the three alternatives a, b, c forming the cycle
   - Prove distinctness: a ≠ b, b ≠ c, c ≠ a
   - Prove P (F p) a b (using decisiveness or unanimity)
   - Prove P (F p) b c
   - Prove P (F p) c a

4. [ ] Alternative: SAT-based verification
   - Encode the problem as a Boolean formula
   - Generate LRAT certificate with external solver
   - Use `bv_check` to verify (see SAT.lean)

-/

end SocialChoiceAtlas.Sen.BaseCase24
