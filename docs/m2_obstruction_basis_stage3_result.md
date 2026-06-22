# M2 Obstruction Basis Stage 3 Result

## 1. Baseline

- Branch: `codex/m2-obstruction-bridge-stage3`
- Starting HEAD: `3dbac73169db08b89bc0015c40447156c6c16b25`
- `origin/main`: `73c891fa3edd96148238570f16453c484fccf283`
- Stage 1 commit: `c53bf57 feat(m2): add generic Sen obstruction witness classification`
- Stage 2 commits:
  - `6b98d7c feat(m2): add generic obstruction profile constructions`
  - `3dbac73 feat(m2): prove Sen obstruction shape soundness`

## 2. Files

Created:

- `SocialChoiceAtlas/Sen/ObstructionBridge.lean`
- `docs/m2_obstruction_basis_stage3_result.md`

Modified:

- `SocialChoiceAtlas/Sen/Lifting/ImpossibilityLift.lean`
- `SocialChoiceAtlas.lean`
- `scripts/ci_m2_smoke.sh`
- `papers/m2/CLAIM_BOUNDARY.md`
- `papers/m2/README.md`
- `papers/m2/REPRODUCIBILITY.md`
- `papers/m2/Makefile`
- `papers/m2/main.tex`
- `papers/m2/sections/00_abstract.tex`
- `papers/m2/sections/01_intro.tex`
- `papers/m2/sections/02_scope_and_shared_infrastructure.tex`
- `papers/m2/sections/03_methods_and_artifacts.tex`
- `papers/m2/sections/03b_contributions.tex`
- `papers/m2/sections/04_results_plan.tex`
- `papers/m2/sections/05_related_work_and_positioning.tex`
- `papers/m2/sections/06_next_steps.tex`
- `papers/m2/sections/appendix_repro.tex`

Protected files unchanged:

- `Certificates/**`
- `results/**`
- `paper/**`
- `papers/m1_5/**`
- `papers/m2_1/**`
- `papers/m3/**`
- `SocialChoiceAtlas/Sen/BaseCase24/**`
- `docs/m2_scope_wall.md`

## 3. Completed Dependency Chain

```text
MINLIB
  -> exists_classified_senRightsWitness
  -> ClassifiedSenRightsWitness
  -> outcome_of_classifiedWitness
  -> SenOutcomeObstruction
  -> SenOutcomeObstruction.refutes_socialAcyclic
  -> ¬ SocialAcyclic
```

Completed layers:

- Extraction: `exists_senRightsWitness`, `exists_classified_senRightsWitness`
- Classification: `classify_raw_overlap`, `ClassifiedSenRightsWitness.kind`
- Exact cardinality: `ClassifiedSenRightsWitness.support_card_eq_kind`
- Soundness: `outcome_of_twoOverlap`, `outcome_of_zOnly`, `outcome_of_wOnly`, `outcome_of_disjoint`
- Outcome refutation: `SenOutcomeObstruction.refutes_socialAcyclic`
- Generic bridge: `sen_outcome_obstruction_of_UN_MINLIB`
- Generic impossibility: `sen_impossibility_from_obstruction_basis`
- Legacy corollary: `sen_impossibility_lifts`

## 4. New Public Theorems

Path: `SocialChoiceAtlas/Sen/ObstructionBridge.lean`

```lean
theorem sen_outcome_obstruction_of_UN_MINLIB
    {Voter : Type u}
    {Alt : Type v}
    [DecidableEq Alt]
    [Fintype Alt]
    (F : SWF Voter Alt)
    (hUN : UN F)
    (hMINLIB : MINLIB F) :
    SenOutcomeObstruction F
```

```lean
theorem sen_impossibility_from_obstruction_basis
    {Voter : Type u}
    {Alt : Type v}
    [DecidableEq Alt]
    [Fintype Alt]
    (F : SWF Voter Alt)
    (hUN : UN F)
    (hMINLIB : MINLIB F) :
    ¬ SocialAcyclic F
```

Path: `SocialChoiceAtlas/Sen/Lifting/ImpossibilityLift.lean`

```lean
theorem sen_impossibility_lifts
    {n m : ℕ} (_hn : 2 ≤ n) (_hm : 4 ≤ m)
    (F : SWF (Fin n) (Fin m))
    (hUN : UN F) (hMINLIB : MINLIB F) :
    ¬ SocialAcyclic F
```

## 5. Genericity

- Voter assumptions: arbitrary `Type u`.
- Absent voter assumptions: no `Fintype Voter`, no `Finite Voter`, no `DecidableEq Voter`.
- Alternative assumptions: arbitrary `Type v` with `[DecidableEq Alt]` and `[Fintype Alt]`.
- Absent size assumptions: no explicit `2 ≤ n`, `4 ≤ m`, or finite-voter lower bound in the generic theorem.

## 6. Legacy Compatibility

- Preserved theorem name: `SocialChoiceAtlas.Sen.Lifting.sen_impossibility_lifts`.
- Preserved statement shape: `{n m : ℕ} (_hn : 2 ≤ n) (_hm : 4 ≤ m) ...`.
- New proof dependency: `SocialChoiceAtlas.Sen.sen_impossibility_from_obstruction_basis`.
- `_hn` / `_hm` status: retained for API compatibility only; unused by the corollary proof.
- Non-claim: this does not mean `UN ∧ MINLIB` implies `4 ≤ m`.

## 7. Meaning of Finite Semantic Obstruction Basis

"Finite semantic obstruction basis" means a complete finite generating family
of semantic obstruction shapes.

- Completeness: every `MINLIB` witness is classified into O2, O3, or O4.
- Finiteness: the family has exactly the three canonical support kinds O2/O3/O4.
- Support cardinalities:
  - O2: support cardinality 2.
  - O3: support cardinality 3.
  - O4: support cardinality 4.
- Outcomes:
  - O2: strict conflict.
  - O3: 3-cycle.
  - O4: 4-cycle.
- Minimality claimed: no.
- Irredundancy claimed: no.
- Uniqueness claimed: no.

## 8. Sen24 Connection

- The connection is semantic shape correspondence: the O2/O3/O4 patterns are the bounded obstruction patterns also visible in the Sen24 proof.
- No literal subinstance claim is made.
- No claim is made that every general instance contains a literal two-voter Sen24 SWF restriction.
- No CNF artifact input claim is made.
- The general theorem is not obtained by treating the Sen24 CNF as a formal premise.

## 9. Scope Wall

- CNF: the Sen24 CNF atlas remains base-case scoped.
- LRAT: the Sen24 LRAT certificate remains a base-case artifact.
- Atlas: no family-level atlas transfer is claimed.
- Repair/MCS: no repair-family, MUS/MCS geometry, or representation-canonicity transfer is claimed.
- `docs/m2_scope_wall.md` was not modified.

## 10. Root and CI Integration

Root imports:

```lean
import SocialChoiceAtlas.Sen.ObstructionBridge
import SocialChoiceAtlas.Sen.Lifting.ImpossibilityLift
```

CI gates in `scripts/ci_m2_smoke.sh` now check:

- Stage 1/2/3 obstruction files exist.
- Root imports include `ObstructionBridge` and `Lifting.ImpossibilityLift`.
- Theorem anchors for `sen_outcome_obstruction_of_`, `sen_impossibility_from_obstruction_basis`, and `sen_impossibility_lifts`.
- The legacy module references `sen_impossibility_from_obstruction_basis`.
- Placeholder scan over the obstruction and legacy lift modules.
- Build targets for `SocialChoiceAtlas.Sen.ObstructionBridge` and `SocialChoiceAtlas.Sen.Lifting.ImpossibilityLift`.

## 11. Manuscript Changes

- Files updated: `papers/m2/CLAIM_BOUNDARY.md`, `papers/m2/README.md`, `papers/m2/REPRODUCIBILITY.md`, `papers/m2/main.tex`, and M2 section files.
- Framing changed from direct proof-port emphasis to finite semantic obstruction bridge emphasis.
- Title status: updated to "A Finite Semantic Obstruction Basis for Sen's Liberal Paradox: A Kernel-Checked Proof-Layer Bridge and Its Artifact Boundary".
- Claim boundary: updated to three authorized claims.
- Main theorem section: updated with T1-T8 theorem ladder.
- Scope wall: preserved and reiterated.

## 12. Axiom Audit

Command used a temporary `/tmp` Lean file with `#check` and `#print axioms`.

Signatures audited:

```text
SocialChoiceAtlas.Sen.sen_outcome_obstruction_of_UN_MINLIB.{u, v}
  {Voter : Type u} {Alt : Type v} [DecidableEq Alt] [Fintype Alt]
  (F : SWF Voter Alt) (hUN : UN F) (hMINLIB : MINLIB F) :
  SenOutcomeObstruction F

SocialChoiceAtlas.Sen.sen_impossibility_from_obstruction_basis.{u, v}
  {Voter : Type u} {Alt : Type v} [DecidableEq Alt] [Fintype Alt]
  (F : SWF Voter Alt) (hUN : UN F) (hMINLIB : MINLIB F) :
  ¬ SocialAcyclic F

SocialChoiceAtlas.Sen.Lifting.sen_impossibility_lifts
  {n m : ℕ} (_hn : 2 ≤ n) (_hm : 4 ≤ m)
  (F : SWF (Fin n) (Fin m)) (hUN : UN F) (hMINLIB : MINLIB F) :
  ¬ SocialAcyclic F
```

Axiom output:

```text
sen_outcome_obstruction_of_UN_MINLIB:
  [propext, Classical.choice, Quot.sound]
sen_impossibility_from_obstruction_basis:
  [propext, Classical.choice, Quot.sound]
sen_impossibility_lifts:
  [propext, Classical.choice, Quot.sound]
```

No custom axiom or `sorryAx` appeared.

## 13. Validation

Formal validation before manuscript changes:

- `lake env lean SocialChoiceAtlas/Sen/ObstructionBasis.lean`: passed.
- `lake env lean SocialChoiceAtlas/Sen/ObstructionProfiles.lean`: passed.
- `lake env lean SocialChoiceAtlas/Sen/ObstructionSoundness.lean`: passed.
- `lake env lean SocialChoiceAtlas/Sen/ObstructionBridge.lean`: passed.
- `lake env lean SocialChoiceAtlas/Sen/Lifting/ImpossibilityLift.lean`: passed.
- `./scripts/ci_m2_smoke.sh`: passed.
- `lake build`: passed, with existing BaseCase24 linter warnings only.

Final validation after documentation edits:

- `lake env lean SocialChoiceAtlas/Sen/ObstructionBasis.lean`: passed.
- `lake env lean SocialChoiceAtlas/Sen/ObstructionProfiles.lean`: passed.
- `lake env lean SocialChoiceAtlas/Sen/ObstructionSoundness.lean`: passed.
- `lake env lean SocialChoiceAtlas/Sen/ObstructionBridge.lean`: passed.
- `lake env lean SocialChoiceAtlas/Sen/Lifting/ImpossibilityLift.lean`: passed.
- `./scripts/ci_m2_smoke.sh`: passed.
- `lake build`: passed, with existing BaseCase24 linter warnings only.
- `make -C papers/m2 pdf`: passed.
- PDF log scan for undefined references/citations and fatal errors: no matches.
- Forbidden-token scan: no matches.
- Dependency scan for forbidden bridge dependencies: no matches.
- PDF text extraction: new finite semantic obstruction bridge title and framing present.
- `git diff --check`: passed.

## 14. Stage 3 Verdict

PASS.

## 15. Remaining Work

- Legacy helper cleanup in `ImpossibilityLift.lean` can be handled as a separate reviewable cleanup.
- Literature novelty audit remains outside this implementation task.
- Submission review remains required after PDF inspection.
- No Arrow obligation is introduced.
- No CNF/LRAT/atlas/repair transfer is claimed.
