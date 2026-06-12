import SocialChoiceAtlas.Reportability.Atomic

/-!
# M3-B: non-atomic group-sound reportability

This file implements the non-atomic sufficient-condition chain.

| Document lemma | Lean declaration |
| --- | --- |
| M3-B B1 contract repair appears in grouped raw image | `contractRepair_isRawGroup` |
| M3-B B2 grouped raw reports are contract-feasible | `rawRepair_group_contractFeasible` |
| M3-B B3 grouped raw reports contain contract-minimal repairs | `isRawGroup_contains_contractRepair` |
| M3-B B4 minimized grouped image equals ContractRep | `groupedRepair_iff_contractRepair` |
| M3-B grouped correctness theorem | `m3b_grouped_correctness` |
| M3-B two-realization corollary | `m3b_two_realization` |

No theorem in this file assumes deletion-monotonicity of `SatPhi`.
-/

namespace SocialChoiceAtlas.Reportability

variable {Atom Lever : Type*} [DecidableEq Atom] [DecidableEq Lever]

/--
M3-B B1: every contract repair occurs as the group of some raw minimal repair.

Finite descent starts from the feasible block deletion.  Group soundness and
contract minimality force the descended raw repair to group back to the
original contract repair.  Atomicity is not assumed.
-/
theorem contractRepair_isRawGroup
    {I G : Finset Atom} {beta : Atom → Finset Lever}
    {SatPsi : Finset Atom → Prop} {SatPhi : Finset Lever → Prop}
    (hDisjoint : BlocksDisjoint I beta)
    (hFaith : ResidualFaithfulness I beta SatPsi SatPhi)
    (hSound : GroupSoundness I beta SatPsi SatPhi)
    (hContract : ContractRepair I SatPsi G) :
    IsRawGroup I beta SatPhi G := by
  have hBlockFeasible :
      RawFeasible I beta SatPhi (betaSet beta G) := by
    refine ⟨betaSet_subset_LambdaI hContract.1.1, ?_⟩
    exact (residual_feasibility_iff
      hDisjoint hFaith hContract.1.1).mpr hContract.1.2
  obtain ⟨R0, hR0sub, hR0Repair⟩ :=
    exists_minimal_raw_subset hBlockFeasible.1 hBlockFeasible.2
  have hGroupSub : groupTouchAny I beta R0 ⊆ G :=
    groupTouchAny_subset_of_subset_betaSet
      hDisjoint hContract.1.1 hR0sub
  have hGroupFeasible :
      ContractFeasible I SatPsi (groupTouchAny I beta R0) := by
    refine ⟨groupTouchAny_subset_I, ?_⟩
    exact hSound R0 hR0Repair.1.1 hR0Repair.1.2
  have hGSub : G ⊆ groupTouchAny I beta R0 :=
    hContract.2 (groupTouchAny I beta R0) hGroupFeasible hGroupSub
  exact ⟨R0, hR0Repair, Finset.Subset.antisymm hGroupSub hGSub⟩

/--
M3-B B2: a raw repair groups to a feasible contract deletion under
`GroupSoundness`.
-/
theorem rawRepair_group_contractFeasible
    {I : Finset Atom} {beta : Atom → Finset Lever}
    {SatPsi : Finset Atom → Prop} {SatPhi : Finset Lever → Prop}
    (hSound : GroupSoundness I beta SatPsi SatPhi)
    {R : Finset Lever} (hRaw : RawRepair I beta SatPhi R) :
    ContractFeasible I SatPsi (groupTouchAny I beta R) := by
  exact ⟨groupTouchAny_subset_I, hSound R hRaw.1.1 hRaw.1.2⟩

/--
M3-B B3: every member of the grouped raw image contains a contract-minimal
repair.
-/
theorem isRawGroup_contains_contractRepair
    {I G : Finset Atom} {beta : Atom → Finset Lever}
    {SatPsi : Finset Atom → Prop} {SatPhi : Finset Lever → Prop}
    (hSound : GroupSoundness I beta SatPsi SatPhi)
    (hGroup : IsRawGroup I beta SatPhi G) :
    ∃ G0, G0 ⊆ G ∧ ContractRepair I SatPsi G0 := by
  obtain ⟨R, hRaw, hEq⟩ := hGroup
  have hFeasible :=
    rawRepair_group_contractFeasible hSound hRaw
  rw [hEq] at hFeasible
  exact exists_minimal_contract_subset hFeasible.1 hFeasible.2

/--
M3-B B4: after minimizing the grouped raw image, the result is exactly the
contract repair family.
-/
theorem groupedRepair_iff_contractRepair
    {I G : Finset Atom} {beta : Atom → Finset Lever}
    {SatPsi : Finset Atom → Prop} {SatPhi : Finset Lever → Prop}
    (hDisjoint : BlocksDisjoint I beta)
    (hFaith : ResidualFaithfulness I beta SatPsi SatPhi)
    (hSound : GroupSoundness I beta SatPsi SatPhi) :
    GroupedRepair I beta SatPhi G ↔ ContractRepair I SatPsi G := by
  constructor
  · intro hGrouped
    obtain ⟨G0, hG0G, hG0Contract⟩ :=
      isRawGroup_contains_contractRepair hSound hGrouped.1
    have hG0Group :=
      contractRepair_isRawGroup hDisjoint hFaith hSound hG0Contract
    have hGG0 := hGrouped.2 G0 hG0Group hG0G
    have hEq := Finset.Subset.antisymm hGG0 hG0G
    simpa [hEq] using hG0Contract
  · intro hContract
    have hGroup :=
      contractRepair_isRawGroup hDisjoint hFaith hSound hContract
    refine ⟨hGroup, ?_⟩
    intro H hHGroup hHG
    obtain ⟨G0, hG0H, hG0Contract⟩ :=
      isRawGroup_contains_contractRepair hSound hHGroup
    have hG0G : G0 ⊆ G := hG0H.trans hHG
    have hGG0 := hContract.2 G0 hG0Contract.1 hG0G
    exact hGG0.trans hG0H

/--
M3-B grouped correctness: residual faithfulness and group soundness suffice for
pointwise equality between grouped implementation repairs and contract repairs.

This theorem is the abstract result used by the artifact-backed Candidate B
interpretation.  The Candidate B use depends on the artifact audit establishing
the complete raw-repair family and grouped image; this Lean theorem does not
formalize the artifact enumeration itself.
-/
theorem m3b_grouped_correctness
    {I : Finset Atom} {beta : Atom → Finset Lever}
    {SatPsi : Finset Atom → Prop} {SatPhi : Finset Lever → Prop}
    (hDisjoint : BlocksDisjoint I beta)
    (hFaith : ResidualFaithfulness I beta SatPsi SatPhi)
    (hSound : GroupSoundness I beta SatPsi SatPhi) :
    ∀ G, GroupedRepair I beta SatPhi G ↔ ContractRepair I SatPsi G := by
  intro G
  exact groupedRepair_iff_contractRepair hDisjoint hFaith hSound

/--
M3-B two-realization corollary: two group-sound, residually faithful
realizations of the same contract have pointwise equivalent grouped reports.
-/
theorem m3b_two_realization
    {Lever₁ Lever₂ : Type*}
    [DecidableEq Lever₁] [DecidableEq Lever₂]
    {I : Finset Atom}
    {beta₁ : Atom → Finset Lever₁} {beta₂ : Atom → Finset Lever₂}
    {SatPsi : Finset Atom → Prop}
    {SatPhi₁ : Finset Lever₁ → Prop} {SatPhi₂ : Finset Lever₂ → Prop}
    (hDisjoint₁ : BlocksDisjoint I beta₁)
    (hDisjoint₂ : BlocksDisjoint I beta₂)
    (hFaith₁ : ResidualFaithfulness I beta₁ SatPsi SatPhi₁)
    (hFaith₂ : ResidualFaithfulness I beta₂ SatPsi SatPhi₂)
    (hSound₁ : GroupSoundness I beta₁ SatPsi SatPhi₁)
    (hSound₂ : GroupSoundness I beta₂ SatPsi SatPhi₂) :
    ∀ G, GroupedRepair I beta₁ SatPhi₁ G ↔
      GroupedRepair I beta₂ SatPhi₂ G := by
  intro G
  rw [m3b_grouped_correctness hDisjoint₁ hFaith₁ hSound₁ G]
  exact (m3b_grouped_correctness
    hDisjoint₂ hFaith₂ hSound₂ G).symm

end SocialChoiceAtlas.Reportability
