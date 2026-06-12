import SocialChoiceAtlas.Reportability.Monotone

/-!
# Kernel-checked M3 boundary examples

The examples are finite truth-table instances over `Fin` types.

* `NonAtomic` checks that group soundness is strictly weaker than repair
  atomicity.
* `NonMonotone` checks that M3-C's reference monotonicity hypothesis cannot be
  removed.

They formalize only the abstract finite-set predicates.  They are not SAT/CNF
encodings and do not formalize the Candidate B artifact audit.
-/

namespace SocialChoiceAtlas.Reportability.Examples

open SocialChoiceAtlas.Reportability

namespace NonAtomic

abbrev Atom := Fin 1
abbrev Lever := Fin 2

local instance : Fintype (Finset Atom) :=
  ⟨Finset.univ.powerset, by
    intro T
    exact Finset.mem_powerset.mpr (Finset.subset_univ T)⟩

local instance : Fintype (Finset Lever) :=
  ⟨Finset.univ.powerset, by
    intro T
    exact Finset.mem_powerset.mpr (Finset.subset_univ T)⟩

def I : Finset Atom := Finset.univ

def beta (_ : Atom) : Finset Lever := Finset.univ

def SatPsi (T : Finset Atom) : Prop := T = ∅

def SatPhi (L : Finset Lever) : Prop := L ≠ Finset.univ

instance (T : Finset Atom) : Decidable (SatPsi T) := by
  unfold SatPsi
  infer_instance

instance (L : Finset Lever) : Decidable (SatPhi L) := by
  unfold SatPhi
  infer_instance

theorem blocksDisjoint : BlocksDisjoint I beta := by
  unfold BlocksDisjoint
  native_decide

theorem blocksNonempty : BlocksNonempty I beta := by
  unfold BlocksNonempty
  native_decide

/-- The one contract atom is represented by a two-lever block. -/
theorem repairAtomicity_fails : ¬ RepairAtomicity I beta := by
  unfold RepairAtomicity
  native_decide

/-- The two block-aligned residuals agree with the reference contract. -/
theorem residualFaithfulness :
    ResidualFaithfulness I beta SatPsi SatPhi := by
  unfold ResidualFaithfulness
  native_decide

/--
Every feasible implementation deletion touches the sole contract atom, so its
grouped contract residual retains no atoms and is feasible.
-/
theorem groupSoundness :
    GroupSoundness I beta SatPsi SatPhi := by
  unfold GroupSoundness
  native_decide

end NonAtomic

namespace NonMonotone

abbrev Atom := Fin 2
abbrev Lever := Fin 3

local instance : Fintype (Finset Atom) :=
  ⟨Finset.univ.powerset, by
    intro T
    exact Finset.mem_powerset.mpr (Finset.subset_univ T)⟩

local instance : Fintype (Finset Lever) :=
  ⟨Finset.univ.powerset, by
    intro T
    exact Finset.mem_powerset.mpr (Finset.subset_univ T)⟩

def a : Atom := 0
def b : Atom := 1
def x1 : Lever := 0
def x2 : Lever := 1
def y : Lever := 2

def I : Finset Atom := Finset.univ

def beta (z : Atom) : Finset Lever :=
  if z = a then {x1, x2} else {y}

def SatPhi (L : Finset Lever) : Prop := x1 ∉ L

def SatPsi (T : Finset Atom) : Prop := T = {b}

instance (L : Finset Lever) : Decidable (SatPhi L) := by
  unfold SatPhi
  infer_instance

instance (T : Finset Atom) : Decidable (SatPsi T) := by
  unfold SatPsi
  infer_instance

theorem blocksDisjoint : BlocksDisjoint I beta := by
  unfold BlocksDisjoint
  native_decide

theorem blocksNonempty : BlocksNonempty I beta := by
  unfold BlocksNonempty
  native_decide

/-- The unique raw minimal deletion is `{x1}`. -/
theorem rawRepair_iff (R : Finset Lever) :
    RawRepair I beta SatPhi R ↔ R = {x1} := by
  unfold RawRepair InclusionMinimal RawFeasible
  native_decide +revert

/-- The unique contract repair is `{a}`. -/
theorem contractRepair_iff (G : Finset Atom) :
    ContractRepair I SatPsi G ↔ G = {a} := by
  unfold ContractRepair InclusionMinimal ContractFeasible
  native_decide +revert

/-- The grouped raw image contains exactly `{a}`. -/
theorem isRawGroup_iff (G : Finset Atom) :
    IsRawGroup I beta SatPhi G ↔ G = {a} := by
  constructor
  · rintro ⟨R, hRaw, rfl⟩
    have hR : R = {x1} := (rawRepair_iff R).mp hRaw
    subst R
    native_decide
  · intro hG
    subst G
    refine ⟨{x1}, (rawRepair_iff {x1}).mpr rfl, ?_⟩
    native_decide

/-- The unique grouped repair is also `{a}`. -/
theorem groupedRepair_iff (G : Finset Atom) :
    GroupedRepair I beta SatPhi G ↔ G = {a} := by
  constructor
  · intro hGrouped
    exact (isRawGroup_iff G).mp hGrouped.1
  · intro hG
    subst G
    refine ⟨(isRawGroup_iff {a}).mpr rfl, ?_⟩
    intro H hH _
    have hEq : H = {a} := (isRawGroup_iff H).mp hH
    simpa [hEq]

/--
Grouped correctness holds pointwise even though the reference predicate is not
deletion-monotone.
-/
theorem grouped_correctness :
    ∀ G, GroupedRepair I beta SatPhi G ↔ ContractRepair I SatPsi G := by
  intro G
  rw [groupedRepair_iff, contractRepair_iff]

/--
Group soundness fails at the deletion `{x1, y}`: the retained implementation
set `{x2}` is feasible, while the grouped reference residual is empty and is
not feasible.
-/
theorem groupSoundness_fails :
    ¬ GroupSoundness I beta SatPsi SatPhi := by
  unfold GroupSoundness
  native_decide

/-- Reference deletion monotonicity fails from retained `{b}` to retained `∅`. -/
theorem psiDeletionMonotonicity_fails :
    ¬ PsiDeletionMonotonicity I SatPsi := by
  unfold PsiDeletionMonotonicity
  native_decide

end NonMonotone

end SocialChoiceAtlas.Reportability.Examples
