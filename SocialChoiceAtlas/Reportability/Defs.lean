import Mathlib

/-!
# M3 reportability definitions

This module is the kernel-checked core for the M3 paper.  Its abstraction
boundary is deliberately small:

* The development is purely at the finite-set level.  `Atom` and `Lever` need
  decidable equality, but no global `Fintype`; every finite quantification is
  bounded by an explicit `Finset`.
* Contract and implementation feasibility are abstract retained-set predicates
  `SatPsi : Finset Atom → Prop` and `SatPhi : Finset Lever → Prop`.
* All core definitions use retained active sets.  Deleting `R` from the active
  implementation interface is written `SatPhi (LambdaI I beta \ R)`, and
  deleting `G` from the contract is written `SatPsi (I \ G)`.
* CNF encodings, SAT solving, LRAT checking, model validation, and the
  artifact-backed Candidate B audit are outside this module.

The mathematical objects remain explicit arguments rather than being hidden in
a global instance.  This makes theorem hypotheses auditable and permits
two-realization statements with different lever types.
-/

namespace SocialChoiceAtlas.Reportability

variable {Atom Lever : Type*} [DecidableEq Atom] [DecidableEq Lever]

/-- The implementation levers contributed by a finite set of contract atoms. -/
def betaSet (beta : Atom → Finset Lever) (T : Finset Atom) : Finset Lever :=
  T.biUnion beta

/-- The active implementation interface induced by all active contract atoms. -/
def LambdaI (I : Finset Atom) (beta : Atom → Finset Lever) : Finset Lever :=
  betaSet beta I

/--
`X` is an inclusion-minimal finite set satisfying `P`.

The final clause is antisymmetry in implication form: every feasible subset of
`X` contains `X`, hence equals it.
-/
def InclusionMinimal {α : Type*} [DecidableEq α]
    (P : Finset α → Prop) (X : Finset α) : Prop :=
  P X ∧ ∀ Y, P Y → Y ⊆ X → X ⊆ Y

/-- Pairwise disjoint active implementation blocks. -/
def BlocksDisjoint (I : Finset Atom) (beta : Atom → Finset Lever) : Prop :=
  ∀ ⦃a b : Atom⦄, a ∈ I → b ∈ I → a ≠ b → Disjoint (beta a) (beta b)

/-- Every active contract atom contributes at least one implementation lever. -/
def BlocksNonempty (I : Finset Atom) (beta : Atom → Finset Lever) : Prop :=
  ∀ a ∈ I, (beta a).Nonempty

/-- Feasibility of deleting `R` from the active implementation interface. -/
def RawFeasible (I : Finset Atom) (beta : Atom → Finset Lever)
    (SatPhi : Finset Lever → Prop) (R : Finset Lever) : Prop :=
  R ⊆ LambdaI I beta ∧ SatPhi (LambdaI I beta \ R)

/-- Inclusion-minimal implementation-level deletion restoring feasibility. -/
def RawRepair (I : Finset Atom) (beta : Atom → Finset Lever)
    (SatPhi : Finset Lever → Prop) (R : Finset Lever) : Prop :=
  InclusionMinimal (RawFeasible I beta SatPhi) R

/-- Touch-any grouping from implementation deletions to active contract atoms. -/
def groupTouchAny (I : Finset Atom) (beta : Atom → Finset Lever)
    (R : Finset Lever) : Finset Atom :=
  I.filter fun a => (R ∩ beta a).Nonempty

/-- Feasibility of deleting `G` from the active contract interface. -/
def ContractFeasible (I : Finset Atom) (SatPsi : Finset Atom → Prop)
    (G : Finset Atom) : Prop :=
  G ⊆ I ∧ SatPsi (I \ G)

/-- Inclusion-minimal contract-level deletion restoring feasibility. -/
def ContractRepair (I : Finset Atom) (SatPsi : Finset Atom → Prop)
    (G : Finset Atom) : Prop :=
  InclusionMinimal (ContractFeasible I SatPsi) G

/-- `G` occurs as the touch-any image of a raw minimal repair. -/
def IsRawGroup (I : Finset Atom) (beta : Atom → Finset Lever)
    (SatPhi : Finset Lever → Prop) (G : Finset Atom) : Prop :=
  ∃ R, RawRepair I beta SatPhi R ∧ groupTouchAny I beta R = G

/-- Inclusion-minimal element of the grouped raw-repair image. -/
def GroupedRepair (I : Finset Atom) (beta : Atom → Finset Lever)
    (SatPhi : Finset Lever → Prop) (G : Finset Atom) : Prop :=
  InclusionMinimal (IsRawGroup I beta SatPhi) G

/-- Agreement of implementation and reference residuals on block-aligned sets. -/
def ResidualFaithfulness (I : Finset Atom) (beta : Atom → Finset Lever)
    (SatPsi : Finset Atom → Prop) (SatPhi : Finset Lever → Prop) : Prop :=
  ∀ T, T ⊆ I → (SatPhi (betaSet beta T) ↔ SatPsi T)

/-- Every active contract atom is represented by exactly one lever. -/
def RepairAtomicity (I : Finset Atom) (beta : Atom → Finset Lever) : Prop :=
  ∀ a ∈ I, (beta a).card = 1

/-- Every feasible implementation deletion remains feasible after grouping. -/
def GroupSoundness (I : Finset Atom) (beta : Atom → Finset Lever)
    (SatPsi : Finset Atom → Prop) (SatPhi : Finset Lever → Prop) : Prop :=
  ∀ R, R ⊆ LambdaI I beta → SatPhi (LambdaI I beta \ R) →
    SatPsi (I \ groupTouchAny I beta R)

/-- Deleting more contract atoms cannot destroy reference satisfiability. -/
def PsiDeletionMonotonicity (I : Finset Atom)
    (SatPsi : Finset Atom → Prop) : Prop :=
  ∀ T' T, T' ⊆ T → T ⊆ I → SatPsi T → SatPsi T'

theorem inclusionMinimal_congr
    {α : Type*} [DecidableEq α] {P Q : Finset α → Prop}
    (hPQ : ∀ X, P X ↔ Q X) {X : Finset α} :
    InclusionMinimal P X ↔ InclusionMinimal Q X := by
  constructor
  · intro h
    refine ⟨(hPQ X).mp h.1, ?_⟩
    intro Y hQY hYX
    exact h.2 Y ((hPQ Y).mpr hQY) hYX
  · intro h
    refine ⟨(hPQ X).mpr h.1, ?_⟩
    intro Y hPY hYX
    exact h.2 Y ((hPQ Y).mp hPY) hYX

theorem inclusionMinimal_idempotent
    {α : Type*} [DecidableEq α] {P : Finset α → Prop}
    {X : Finset α} :
    InclusionMinimal (InclusionMinimal P) X ↔ InclusionMinimal P X := by
  constructor
  · exact fun h => h.1
  · intro h
    refine ⟨h, ?_⟩
    intro Y hY hYX
    exact h.2 Y hY.1 hYX

theorem betaSet_subset_LambdaI
    {I T : Finset Atom} {beta : Atom → Finset Lever}
    (hT : T ⊆ I) :
    betaSet beta T ⊆ LambdaI I beta := by
  intro x hx
  simp only [betaSet, LambdaI, Finset.mem_biUnion] at hx ⊢
  obtain ⟨a, haT, hxa⟩ := hx
  exact ⟨a, hT haT, hxa⟩

theorem groupTouchAny_mono
    {I : Finset Atom} {beta : Atom → Finset Lever} {R₀ R : Finset Lever}
    (hR : R₀ ⊆ R) :
    groupTouchAny I beta R₀ ⊆ groupTouchAny I beta R := by
  intro a ha
  simp only [groupTouchAny, Finset.mem_filter] at ha ⊢
  refine ⟨ha.1, ?_⟩
  rcases ha.2 with ⟨x, hx⟩
  have ⟨hxR₀, hxbeta⟩ := Finset.mem_inter.mp hx
  exact ⟨x, Finset.mem_inter.mpr ⟨hR hxR₀, hxbeta⟩⟩

theorem groupTouchAny_subset_I
    {I : Finset Atom} {beta : Atom → Finset Lever} {R : Finset Lever} :
    groupTouchAny I beta R ⊆ I := by
  intro a ha
  exact (Finset.mem_filter.mp ha).1

theorem groupTouchAny_subset_of_subset_betaSet
    {I G : Finset Atom} {beta : Atom → Finset Lever} {R : Finset Lever}
    (hDisjoint : BlocksDisjoint I beta) (hG : G ⊆ I)
    (hR : R ⊆ betaSet beta G) :
    groupTouchAny I beta R ⊆ G := by
  intro a ha
  simp only [groupTouchAny, Finset.mem_filter] at ha
  obtain ⟨haI, x, hx⟩ := ha
  have ⟨hxR, hxa⟩ := Finset.mem_inter.mp hx
  have hxBG : x ∈ betaSet beta G := hR hxR
  simp only [betaSet, Finset.mem_biUnion] at hxBG
  obtain ⟨b, hbG, hxb⟩ := hxBG
  by_contra hab
  have hab' : a ≠ b := by
    intro hEq
    exact hab (hEq ▸ hbG)
  have hd := hDisjoint haI (hG hbG) hab'
  exact Finset.disjoint_left.mp hd hxa hxb

/--
Every feasible finite set contains an inclusion-minimal feasible subset.

The proof is finite descent through strict subsets.  It uses no monotonicity
property of `P`.
-/
theorem exists_inclusionMinimal_subset
    {α : Type*} [DecidableEq α] (P : Finset α → Prop)
    (X : Finset α) (hPX : P X) :
    ∃ Y, Y ⊆ X ∧ InclusionMinimal P Y := by
  classical
  revert hPX
  refine Finset.strongInductionOn X ?_
  intro X ih hPX
  by_cases hsub : ∃ Y, P Y ∧ Y ⊂ X
  · obtain ⟨Y, hPY, hYX⟩ := hsub
    obtain ⟨Z, hZY, hmin⟩ := ih Y hYX hPY
    exact ⟨Z, hZY.trans hYX.subset, hmin⟩
  · refine ⟨X, Finset.Subset.rfl, hPX, ?_⟩
    intro Y hPY hYX
    by_contra hXY
    have hne : Y ≠ X := by
      intro hEq
      subst Y
      exact hXY Finset.Subset.rfl
    exact hsub ⟨Y, hPY, Finset.ssubset_iff_subset_ne.mpr ⟨hYX, hne⟩⟩

/--
Finite descent from an arbitrary feasible implementation deletion to a raw
minimal repair.  No deletion-monotonicity of `SatPhi` is assumed.
-/
theorem exists_minimal_raw_subset
    {I : Finset Atom} {beta : Atom → Finset Lever}
    {SatPhi : Finset Lever → Prop} {R : Finset Lever}
    (hR : R ⊆ LambdaI I beta)
    (hSat : SatPhi (LambdaI I beta \ R)) :
    ∃ R0, R0 ⊆ R ∧ RawRepair I beta SatPhi R0 := by
  exact exists_inclusionMinimal_subset
    (RawFeasible I beta SatPhi) R ⟨hR, hSat⟩

/--
Finite descent in the grouped image.  Every grouped raw report contains an
inclusion-minimal grouped report.
-/
theorem exists_minimal_group_subset
    {I : Finset Atom} {beta : Atom → Finset Lever}
    {SatPhi : Finset Lever → Prop} {G : Finset Atom}
    (hG : IsRawGroup I beta SatPhi G) :
    ∃ G0, G0 ⊆ G ∧ GroupedRepair I beta SatPhi G0 := by
  exact exists_inclusionMinimal_subset
    (IsRawGroup I beta SatPhi) G hG

/-- Finite descent from a feasible contract deletion to a contract repair. -/
theorem exists_minimal_contract_subset
    {I : Finset Atom} {SatPsi : Finset Atom → Prop} {G : Finset Atom}
    (hG : G ⊆ I) (hSat : SatPsi (I \ G)) :
    ∃ G0, G0 ⊆ G ∧ ContractRepair I SatPsi G0 := by
  exact exists_inclusionMinimal_subset
    (ContractFeasible I SatPsi) G ⟨hG, hSat⟩

end SocialChoiceAtlas.Reportability
