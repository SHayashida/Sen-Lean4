import SocialChoiceAtlas.Reportability.Defs

/-!
# M3-A: atomic reportability interfaces

This file implements the atomic sufficient-condition chain.

| Document lemma | Lean declaration |
| --- | --- |
| M3-A L3 complement identity | `betaSet_sdiff` |
| M3-A L2.5 block-alignment closure | `exists_unique_atom_set_of_lever_subset` |
| M3-A L2 atom-indexed bijection | `betaSet_injective_on_active` |
| M3-A L4 feasibility transfer | `residual_feasibility_iff` |
| M3-A L5 minimality transfer | `rawRepair_betaSet_iff_contractRepair` |
| M3-A L6 grouping identity | `groupTouchAny_betaSet` |
| M3-A L7 single-realization correctness | `isRawGroup_iff_contractRepair_of_atomic` |
| M3-A grouped correctness theorem | `m3a_grouped_correctness` |
| M3-A raw transport corollary | `m3a_raw_transport` |
-/

namespace SocialChoiceAtlas.Reportability

variable {Atom Lever : Type*} [DecidableEq Atom] [DecidableEq Lever]

/--
M3-A L3: block-aligned deletion commutes with taking the active complement.

Atomicity is intentionally absent.  Pairwise disjointness and active-domain
coverage are sufficient.
-/
theorem betaSet_sdiff
    {I G : Finset Atom} {beta : Atom → Finset Lever}
    (hDisjoint : BlocksDisjoint I beta) (hG : G ⊆ I) :
    betaSet beta (I \ G) = LambdaI I beta \ betaSet beta G := by
  ext x
  constructor
  · intro hx
    simp only [betaSet, Finset.mem_biUnion] at hx
    obtain ⟨a, haIG, hxa⟩ := hx
    have haI := (Finset.mem_sdiff.mp haIG).1
    have haG := (Finset.mem_sdiff.mp haIG).2
    apply Finset.mem_sdiff.mpr
    refine ⟨?_, ?_⟩
    · simp only [LambdaI, betaSet, Finset.mem_biUnion]
      exact ⟨a, haI, hxa⟩
    · intro hxG
      simp only [betaSet, Finset.mem_biUnion] at hxG
      obtain ⟨b, hbG, hxb⟩ := hxG
      have hab : a ≠ b := by
        intro hEq
        exact haG (hEq ▸ hbG)
      exact Finset.disjoint_left.mp
        (hDisjoint haI (hG hbG) hab) hxa hxb
  · intro hx
    have ⟨hxI, hxG⟩ := Finset.mem_sdiff.mp hx
    simp only [LambdaI, betaSet, Finset.mem_biUnion] at hxI
    obtain ⟨a, haI, hxa⟩ := hxI
    simp only [betaSet, Finset.mem_biUnion]
    refine ⟨a, Finset.mem_sdiff.mpr ⟨haI, ?_⟩, hxa⟩
    intro haG
    apply hxG
    simp only [betaSet, Finset.mem_biUnion]
    exact ⟨a, haG, hxa⟩

/--
M3-A L6: touch-any grouping is a left inverse to the block map on active atom
sets.  This uses disjointness and nonemptiness only, not atomicity.
-/
theorem groupTouchAny_betaSet
    {I G : Finset Atom} {beta : Atom → Finset Lever}
    (hDisjoint : BlocksDisjoint I beta)
    (hNonempty : BlocksNonempty I beta) (hG : G ⊆ I) :
    groupTouchAny I beta (betaSet beta G) = G := by
  ext a
  constructor
  · intro ha
    simp only [groupTouchAny, Finset.mem_filter] at ha
    obtain ⟨haI, x, hx⟩ := ha
    have ⟨hxBG, hxa⟩ := Finset.mem_inter.mp hx
    simp only [betaSet, Finset.mem_biUnion] at hxBG
    obtain ⟨b, hbG, hxb⟩ := hxBG
    by_contra haG
    have hab : a ≠ b := by
      intro hEq
      exact haG (hEq ▸ hbG)
    exact Finset.disjoint_left.mp
      (hDisjoint haI (hG hbG) hab) hxa hxb
  · intro haG
    have haI := hG haG
    obtain ⟨x, hxa⟩ := hNonempty a haI
    simp only [groupTouchAny, Finset.mem_filter]
    refine ⟨haI, ⟨x, Finset.mem_inter.mpr ⟨?_, hxa⟩⟩⟩
    simp only [betaSet, Finset.mem_biUnion]
    exact ⟨a, haG, hxa⟩

/-- Active block sets are injective under disjointness and nonemptiness. -/
theorem betaSet_injective_on_active
    {I G H : Finset Atom} {beta : Atom → Finset Lever}
    (hDisjoint : BlocksDisjoint I beta)
    (hNonempty : BlocksNonempty I beta)
    (hG : G ⊆ I) (hH : H ⊆ I)
    (hEq : betaSet beta G = betaSet beta H) :
    G = H := by
  calc
    G = groupTouchAny I beta (betaSet beta G) :=
      (groupTouchAny_betaSet hDisjoint hNonempty hG).symm
    _ = groupTouchAny I beta (betaSet beta H) := by rw [hEq]
    _ = H := groupTouchAny_betaSet hDisjoint hNonempty hH

/-- Atomic active blocks are nonempty. -/
theorem blocksNonempty_of_atomicity
    {I : Finset Atom} {beta : Atom → Finset Lever}
    (hAtomic : RepairAtomicity I beta) :
    BlocksNonempty I beta := by
  intro a haI
  have hcard := hAtomic a haI
  exact Finset.card_pos.mp (by omega)

private theorem atomic_block_eq_singleton
    {I : Finset Atom} {beta : Atom → Finset Lever}
    (hAtomic : RepairAtomicity I beta)
    {a : Atom} (haI : a ∈ I) {x : Lever} (hxa : x ∈ beta a) :
    beta a = {x} := by
  obtain ⟨y, hy⟩ := Finset.card_eq_one.mp (hAtomic a haI)
  rw [hy] at hxa ⊢
  have hxy : x = y := Finset.mem_singleton.mp hxa
  subst x
  rfl

/--
M3-A L2.5: under atomicity, every deletion from the active lever interface is
the block image of a unique active atom set.
-/
theorem exists_unique_atom_set_of_lever_subset
    {I : Finset Atom} {beta : Atom → Finset Lever}
    (hDisjoint : BlocksDisjoint I beta)
    (hAtomic : RepairAtomicity I beta)
    {R : Finset Lever} (hR : R ⊆ LambdaI I beta) :
    ∃! G, G ⊆ I ∧ R = betaSet beta G := by
  let G := groupTouchAny I beta R
  have hGI : G ⊆ I := groupTouchAny_subset_I
  have hEq : R = betaSet beta G := by
    apply Finset.Subset.antisymm
    · intro x hxR
      have hxI := hR hxR
      simp only [LambdaI, betaSet, Finset.mem_biUnion] at hxI
      obtain ⟨a, haI, hxa⟩ := hxI
      simp only [betaSet, Finset.mem_biUnion]
      refine ⟨a, ?_, hxa⟩
      simp only [G, groupTouchAny, Finset.mem_filter]
      exact ⟨haI, ⟨x, Finset.mem_inter.mpr ⟨hxR, hxa⟩⟩⟩
    · intro x hx
      simp only [betaSet, Finset.mem_biUnion] at hx
      obtain ⟨a, haG, hxa⟩ := hx
      simp only [G, groupTouchAny, Finset.mem_filter] at haG
      obtain ⟨haI, y, hy⟩ := haG
      have ⟨hyR, hya⟩ := Finset.mem_inter.mp hy
      have hblockX := atomic_block_eq_singleton hAtomic haI hxa
      have hxy : x = y := by
        have hyx : y = x := by
          simpa [hblockX] using hya
        exact hyx.symm
      exact hxy ▸ hyR
  refine ⟨G, ⟨hGI, hEq⟩, ?_⟩
  intro H hH
  have hNonempty := blocksNonempty_of_atomicity hAtomic
  exact betaSet_injective_on_active hDisjoint hNonempty
    hH.1 hGI (hH.2.symm.trans hEq)

/--
M3-A L4: residual faithfulness transfers feasibility across a block-aligned
deletion.
-/
theorem residual_feasibility_iff
    {I G : Finset Atom} {beta : Atom → Finset Lever}
    {SatPsi : Finset Atom → Prop} {SatPhi : Finset Lever → Prop}
    (hDisjoint : BlocksDisjoint I beta)
    (hFaith : ResidualFaithfulness I beta SatPsi SatPhi)
    (hG : G ⊆ I) :
    SatPhi (LambdaI I beta \ betaSet beta G) ↔ SatPsi (I \ G) := by
  rw [← betaSet_sdiff hDisjoint hG]
  exact hFaith (I \ G) (Finset.sdiff_subset)

/--
M3-A L5: block-aligned raw minimal repairs correspond exactly to contract
minimal repairs.
-/
theorem rawRepair_betaSet_iff_contractRepair
    {I G : Finset Atom} {beta : Atom → Finset Lever}
    {SatPsi : Finset Atom → Prop} {SatPhi : Finset Lever → Prop}
    (hDisjoint : BlocksDisjoint I beta)
    (hAtomic : RepairAtomicity I beta)
    (hFaith : ResidualFaithfulness I beta SatPsi SatPhi)
    (hG : G ⊆ I) :
    RawRepair I beta SatPhi (betaSet beta G) ↔
      ContractRepair I SatPsi G := by
  have hNonempty := blocksNonempty_of_atomicity hAtomic
  constructor
  · intro hRaw
    refine ⟨?_, ?_⟩
    · exact ⟨hG, (residual_feasibility_iff hDisjoint hFaith hG).mp hRaw.1.2⟩
    · intro H hHF hHG
      have hBH : RawFeasible I beta SatPhi (betaSet beta H) := by
        refine ⟨betaSet_subset_LambdaI hHF.1, ?_⟩
        exact (residual_feasibility_iff hDisjoint hFaith hHF.1).mpr hHF.2
      have hsub : betaSet beta H ⊆ betaSet beta G := by
        intro x hx
        simp only [betaSet, Finset.mem_biUnion] at hx ⊢
        obtain ⟨a, haH, hxa⟩ := hx
        exact ⟨a, hHG haH, hxa⟩
      have hback := hRaw.2 (betaSet beta H) hBH hsub
      intro a haG
      have haGrouped :
          a ∈ groupTouchAny I beta (betaSet beta G) := by
        rw [groupTouchAny_betaSet hDisjoint hNonempty hG]
        exact haG
      have haGroupedH :
          a ∈ groupTouchAny I beta (betaSet beta H) := by
        exact groupTouchAny_mono hback haGrouped
      simpa [groupTouchAny_betaSet hDisjoint hNonempty hHF.1] using haGroupedH
  · intro hContract
    refine ⟨?_, ?_⟩
    · exact ⟨betaSet_subset_LambdaI hG,
        (residual_feasibility_iff hDisjoint hFaith hG).mpr hContract.1.2⟩
    · intro R hRF hRsub
      obtain ⟨H, hHuniq, hHunique⟩ :=
        exists_unique_atom_set_of_lever_subset hDisjoint hAtomic hRF.1
      have hHEq : R = betaSet beta H := hHuniq.2
      have hHG : H ⊆ G := by
        rw [← groupTouchAny_betaSet hDisjoint hNonempty hHuniq.1]
        apply groupTouchAny_subset_of_subset_betaSet hDisjoint hG
        rw [← hHEq]
        exact hRsub
      have hHContract : ContractFeasible I SatPsi H := by
        refine ⟨hHuniq.1, ?_⟩
        apply (residual_feasibility_iff hDisjoint hFaith hHuniq.1).mp
        simpa [hHEq] using hRF.2
      have hGH := hContract.2 H hHContract hHG
      intro x hx
      simp only [betaSet, Finset.mem_biUnion] at hx
      obtain ⟨a, haG, hxa⟩ := hx
      rw [hHEq]
      simp only [betaSet, Finset.mem_biUnion]
      exact ⟨a, hGH haG, hxa⟩

/--
M3-A L7: under atomicity, occurring grouped raw reports are exactly contract
minimal repairs.
-/
theorem isRawGroup_iff_contractRepair_of_atomic
    {I G : Finset Atom} {beta : Atom → Finset Lever}
    {SatPsi : Finset Atom → Prop} {SatPhi : Finset Lever → Prop}
    (hDisjoint : BlocksDisjoint I beta)
    (hAtomic : RepairAtomicity I beta)
    (hFaith : ResidualFaithfulness I beta SatPsi SatPhi) :
    IsRawGroup I beta SatPhi G ↔ ContractRepair I SatPsi G := by
  have hNonempty := blocksNonempty_of_atomicity hAtomic
  constructor
  · rintro ⟨R, hRaw, rfl⟩
    obtain ⟨H, hH, _⟩ :=
      exists_unique_atom_set_of_lever_subset hDisjoint hAtomic hRaw.1.1
    have hRawH : RawRepair I beta SatPhi (betaSet beta H) := by
      simpa [hH.2] using hRaw
    have hContract :=
      (rawRepair_betaSet_iff_contractRepair
        hDisjoint hAtomic hFaith hH.1).mp hRawH
    simpa [hH.2, groupTouchAny_betaSet hDisjoint hNonempty hH.1]
      using hContract
  · intro hContract
    have hG := hContract.1.1
    refine ⟨betaSet beta G, ?_, ?_⟩
    · exact (rawRepair_betaSet_iff_contractRepair
        hDisjoint hAtomic hFaith hG).mpr hContract
    · exact groupTouchAny_betaSet hDisjoint hNonempty hG

/--
M3-A grouped correctness: atomicity plus residual faithfulness makes the
grouped implementation repair predicate coincide pointwise with the contract
repair predicate.
-/
theorem m3a_grouped_correctness
    {I : Finset Atom} {beta : Atom → Finset Lever}
    {SatPsi : Finset Atom → Prop} {SatPhi : Finset Lever → Prop}
    (hDisjoint : BlocksDisjoint I beta)
    (hAtomic : RepairAtomicity I beta)
    (hFaith : ResidualFaithfulness I beta SatPsi SatPhi) :
    ∀ G, GroupedRepair I beta SatPhi G ↔ ContractRepair I SatPsi G := by
  intro G
  rw [GroupedRepair]
  refine (inclusionMinimal_congr ?_).trans inclusionMinimal_idempotent
  intro H
  exact isRawGroup_iff_contractRepair_of_atomic hDisjoint hAtomic hFaith

/--
M3-A raw transport corollary: two atomic realizations of the same contract
have equivalent atom-indexed block repairs.  No arbitrary lever-bijection
transport is claimed.
-/
theorem m3a_raw_transport
    {Lever₁ Lever₂ : Type*}
    [DecidableEq Lever₁] [DecidableEq Lever₂]
    {I G : Finset Atom}
    {beta₁ : Atom → Finset Lever₁} {beta₂ : Atom → Finset Lever₂}
    {SatPsi : Finset Atom → Prop}
    {SatPhi₁ : Finset Lever₁ → Prop} {SatPhi₂ : Finset Lever₂ → Prop}
    (hDisjoint₁ : BlocksDisjoint I beta₁)
    (hDisjoint₂ : BlocksDisjoint I beta₂)
    (hAtomic₁ : RepairAtomicity I beta₁)
    (hAtomic₂ : RepairAtomicity I beta₂)
    (hFaith₁ : ResidualFaithfulness I beta₁ SatPsi SatPhi₁)
    (hFaith₂ : ResidualFaithfulness I beta₂ SatPsi SatPhi₂)
    (hG : G ⊆ I) :
    RawRepair I beta₁ SatPhi₁ (betaSet beta₁ G) ↔
      RawRepair I beta₂ SatPhi₂ (betaSet beta₂ G) := by
  rw [rawRepair_betaSet_iff_contractRepair
      hDisjoint₁ hAtomic₁ hFaith₁ hG]
  exact (rawRepair_betaSet_iff_contractRepair
    hDisjoint₂ hAtomic₂ hFaith₂ hG).symm

end SocialChoiceAtlas.Reportability
