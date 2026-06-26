import SocialChoiceAtlas.Reportability.GroupSound

/-!
# M3-C: exactness for deletion-monotone contracts

This file implements the candidate converse and its consequences.

| Document lemma | Lean declaration |
| --- | --- |
| M3-C converse | `m3c_converse` |
| M3-C equivalence corollary | `groupSoundness_iff` |
| Audit-cost collapse lemma | `audit_cost_collapse` |
| M3-A hierarchy lemma | `atomicity_implies_groupSoundness` |

`m3c_converse` does not assume residual faithfulness.  The audit-cost collapse
does not assume deletion-monotonicity of `SatPhi`.
-/

namespace SocialChoiceAtlas.Reportability

variable {Atom Lever : Type*} [DecidableEq Atom] [DecidableEq Lever]

private theorem sdiff_antitone_right
    {α : Type*} [DecidableEq α] {A B C : Finset α}
    (hBC : B ⊆ C) :
    A \ C ⊆ A \ B := by
  intro x hx
  have ⟨hxA, hxC⟩ := Finset.mem_sdiff.mp hx
  exact Finset.mem_sdiff.mpr ⟨hxA, fun hxB => hxC (hBC hxB)⟩

/--
Audit-cost collapse: for a deletion-monotone reference contract, checking
reference feasibility only on raw minimal repairs implies unrestricted group
soundness.

The descent from an arbitrary feasible deletion uses finiteness only.
-/
theorem audit_cost_collapse
    {I : Finset Atom} {beta : Atom → Finset Lever}
    {SatPsi : Finset Atom → Prop} {SatPhi : Finset Lever → Prop}
    (hMono : PsiDeletionMonotonicity I SatPsi)
    (hRaw : ∀ R, RawRepair I beta SatPhi R →
      SatPsi (I \ groupTouchAny I beta R)) :
    GroupSoundness I beta SatPsi SatPhi := by
  intro R hRI hSat
  obtain ⟨R0, hR0R, hR0Repair⟩ :=
    exists_minimal_raw_subset hRI hSat
  have hGroup :
      groupTouchAny I beta R0 ⊆ groupTouchAny I beta R :=
    groupTouchAny_mono hR0R
  exact hMono
    (I \ groupTouchAny I beta R)
    (I \ groupTouchAny I beta R0)
    (sdiff_antitone_right hGroup)
    Finset.sdiff_subset
    (hRaw R0 hR0Repair)

/--
M3-C converse: over a deletion-monotone reference contract, pointwise grouped
correctness implies `GroupSoundness`.

Residual faithfulness is intentionally absent.  The proof descends first to a
raw repair and then to a minimal grouped image before applying the assumed
grouped-correctness equivalence.
-/
theorem m3c_converse
    {I : Finset Atom} {beta : Atom → Finset Lever}
    {SatPsi : Finset Atom → Prop} {SatPhi : Finset Lever → Prop}
    (hMono : PsiDeletionMonotonicity I SatPsi)
    (hCorrect :
      ∀ G, GroupedRepair I beta SatPhi G ↔ ContractRepair I SatPsi G) :
    GroupSoundness I beta SatPsi SatPhi := by
  apply audit_cost_collapse hMono
  intro R hRaw
  have hImage :
      IsRawGroup I beta SatPhi (groupTouchAny I beta R) :=
    ⟨R, hRaw, rfl⟩
  obtain ⟨G0, hG0, hGrouped⟩ :=
    exists_minimal_group_subset hImage
  have hContract : ContractRepair I SatPsi G0 :=
    (hCorrect G0).mp hGrouped
  exact hMono
    (I \ groupTouchAny I beta R)
    (I \ G0)
    (sdiff_antitone_right hG0)
    Finset.sdiff_subset
    hContract.1.2

/--
M3-C equivalence corollary: for residually faithful realizations over
deletion-monotone reference contracts, `GroupSoundness` is equivalent to
pointwise grouped correctness.

Residual faithfulness is used only in the M3-B forward direction.
-/
theorem groupSoundness_iff
    {I : Finset Atom} {beta : Atom → Finset Lever}
    {SatPsi : Finset Atom → Prop} {SatPhi : Finset Lever → Prop}
    (hDisjoint : BlocksDisjoint I beta)
    (hFaith : ResidualFaithfulness I beta SatPsi SatPhi)
    (hMono : PsiDeletionMonotonicity I SatPsi) :
    GroupSoundness I beta SatPsi SatPhi ↔
      ∀ G, GroupedRepair I beta SatPhi G ↔ ContractRepair I SatPsi G := by
  constructor
  · intro hSound
    exact m3b_grouped_correctness hDisjoint hFaith hSound
  · exact m3c_converse hMono

/--
Hierarchy lemma: repair atomicity plus residual faithfulness implies group
soundness.  Thus M3-A is a syntactic special case of the M3-B condition.
-/
theorem atomicity_implies_groupSoundness
    {I : Finset Atom} {beta : Atom → Finset Lever}
    {SatPsi : Finset Atom → Prop} {SatPhi : Finset Lever → Prop}
    (hDisjoint : BlocksDisjoint I beta)
    (hAtomic : RepairAtomicity I beta)
    (hFaith : ResidualFaithfulness I beta SatPsi SatPhi) :
    GroupSoundness I beta SatPsi SatPhi := by
  intro R hRI hSat
  obtain ⟨G, hG, _⟩ :=
    exists_unique_atom_set_of_lever_subset hDisjoint hAtomic hRI
  have hNonempty := blocksNonempty_of_atomicity hAtomic
  have hGrouped :
      groupTouchAny I beta R = G := by
    rw [hG.2]
    exact groupTouchAny_betaSet hDisjoint hNonempty hG.1
  rw [hGrouped]
  apply (residual_feasibility_iff hDisjoint hFaith hG.1).mp
  simpa [hG.2] using hSat

end SocialChoiceAtlas.Reportability
