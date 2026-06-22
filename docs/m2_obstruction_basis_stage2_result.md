# M2 Obstruction Basis Stage 2 Result

## 1. Baseline

- Branch: `codex/m2-obstruction-soundness-stage2`
- Starting HEAD: `c53bf57a7e09b420f6045075379355436ea8a553`
- `origin/main`: `73c891fa3edd96148238570f16453c484fccf283`
- Stage 1 commit: `c53bf57 feat(m2): add generic Sen obstruction witness classification`

## 2. Files

Created:

- `SocialChoiceAtlas/Sen/ObstructionProfiles.lean`
- `SocialChoiceAtlas/Sen/ObstructionSoundness.lean`
- `docs/m2_obstruction_basis_stage2_result.md`

Modified:

- None.

Protected files unchanged:

- `Certificates/**`
- `results/**`
- `paper/**`
- `papers/m1_5/**`
- `papers/m2/**`
- `papers/m2_1/**`
- `papers/m3/**`
- `SocialChoiceAtlas/Sen/BaseCase24/**`
- `SocialChoiceAtlas/Sen/Lifting/ImpossibilityLift.lean`
- `SocialChoiceAtlas.lean`
- `scripts/ci_m2_smoke.sh`
- `docs/m2_scope_wall.md`
- `papers/m2/CLAIM_BOUNDARY.md`

## 3. Generic Profile Infrastructure

`SocialChoiceAtlas/Sen/ObstructionProfiles.lean` provides the Stage 2 generic helpers without importing `ImpossibilityLift.lean`.

Prefix ranking:

- `obstructionRankingOfPrefix`
- `obstructionRanking_position_of_mem_prefix`
- `obstructionRanking_position_getElem`
- `obstructionRanking_prefers_getElem`

The construction completes a `List Alt` prefix by appending the finite ambient complement. It requires finite alternatives because repository rankings are complete finite lists.

Two-ranking ambient profile:

- `twoRankingProfile`
- `twoRankingProfile_apply_j`
- `twoRankingProfile_apply_ne`
- `prefers_i_twoRankingProfile_at_j`
- `prefers_i_twoRankingProfile_at_other`
- `prefers_i_twoRankingProfile_at_i`
- `twoRankingProfile_unanimous`

This is not an exactly-two-voter profile. It is an ambient profile over arbitrary `Voter` using at most two ranking types: voter `j` receives `r_j`, and every other voter receives `r_i`. UN edges are still proved for all voters.

## 4. Exact Support Cardinalities

Exact branch cardinalities are now kernel-checked in `ObstructionSoundness.lean`:

- O2: `SenRightsWitness.support_card_eq_two_of_twoOverlap`
- O3 z-only: `SenRightsWitness.support_card_eq_three_of_zOnly`
- O3 w-only: `SenRightsWitness.support_card_eq_three_of_wOnly`
- O4: `SenRightsWitness.support_card_eq_four_of_disjoint`

Integrated theorem:

- `ClassifiedSenRightsWitness.support_card_eq_kind`

No exact cardinality theorem was deferred.

## 5. Outcome Obstruction Interface

`SenOutcomeObstruction` distinguishes three semantic outcomes:

- `strictConflict`: opposite strict social edges on the same ordered pair;
- `cycle3At`: a 3-cycle in the strict social relation at a profile;
- `cycle4At`: a 4-cycle in the strict social relation at a profile.

Refutation theorem:

```lean
theorem SenOutcomeObstruction.refutes_socialAcyclic
    (o : SenOutcomeObstruction F) :
    ¬ SocialAcyclic F
```

The strict conflict branch uses `strictPart_asymm`; the cycle branches use `cycle3_implies_not_acyclic` and `cycle4_implies_not_acyclic`.

## 6. O2 Soundness

Theorem:

```lean
theorem outcome_of_twoOverlap
    (F : SWF Voter Alt)
    (wit : SenRightsWitness F)
    (hz : wit.z ∈ ({wit.x, wit.y} : Finset Alt))
    (hw : wit.w ∈ ({wit.x, wit.y} : Finset Alt)) :
    SenOutcomeObstruction F
```

Ranking pattern:

- `r_i` begins `[x, y]`.
- `r_j` begins `[y, x]`.

Edges:

- `x P y` from `wit.decisive_i`;
- `y P x` from `wit.decisive_j`, after proving the second pair is `(x,y)` or `(y,x)`.

UN usage: none.

Outcome: `SenOutcomeObstruction.strictConflict`.

## 7. O3 Soundness

z-only theorem:

```lean
theorem outcome_of_zOnly
    (F : SWF Voter Alt)
    (hUN : UN F)
    (wit : SenRightsWitness F)
    (hz : wit.z ∈ ({wit.x, wit.y} : Finset Alt))
    (hw : wit.w ∉ ({wit.x, wit.y} : Finset Alt)) :
    SenOutcomeObstruction F
```

z-only shared-x branch:

- rankings: `[w, y, x]` and `[x, w, y]`;
- edges: `y P x` decisive, `x P w` decisive, `w P y` by UN;
- outcome: 3-cycle `y P x P w P y`.

z-only shared-y branch:

- rankings: `[w, x, y]` and `[y, w, x]`;
- edges: `x P y` decisive, `y P w` decisive, `w P x` by UN;
- outcome: 3-cycle `x P y P w P x`.

w-only theorem:

```lean
theorem outcome_of_wOnly
    (F : SWF Voter Alt)
    (hUN : UN F)
    (wit : SenRightsWitness F)
    (hz : wit.z ∉ ({wit.x, wit.y} : Finset Alt))
    (hw : wit.w ∈ ({wit.x, wit.y} : Finset Alt)) :
    SenOutcomeObstruction F
```

The w-only branch reuses z-only by orientation normalization through:

- `SenRightsWitness.swapSecondPair`;
- `Decisive.symm`.

Thus w-only is not a duplicated soundness proof.

## 8. O4 Soundness

Theorem:

```lean
theorem outcome_of_disjoint
    (F : SWF Voter Alt)
    (hUN : UN F)
    (wit : SenRightsWitness F)
    (hz : wit.z ∉ ({wit.x, wit.y} : Finset Alt))
    (hw : wit.w ∉ ({wit.x, wit.y} : Finset Alt)) :
    SenOutcomeObstruction F
```

Ranking pattern:

- `r_i` begins `[w, x, y, z]`;
- `r_j` begins `[y, z, w, x]`.

Edges:

- `x P y` from `wit.decisive_i`;
- `y P z` from UN;
- `z P w` from `wit.decisive_j`;
- `w P x` from UN.

Outcome: 4-cycle `x P y P z P w P x`.

## 9. Classified Witness Flagship

Stage 2 flagship:

```lean
theorem outcome_of_classifiedWitness
    (F : SWF Voter Alt)
    (hUN : UN F)
    (cw : ClassifiedSenRightsWitness F) :
    SenOutcomeObstruction F
```

Refutation corollary:

```lean
theorem classifiedWitness_not_socialAcyclic
    (F : SWF Voter Alt)
    (hUN : UN F)
    (cw : ClassifiedSenRightsWitness F) :
    ¬ SocialAcyclic F
```

Dependency DAG:

```text
Core / Axioms
  -> ObstructionBasis
  -> ObstructionProfiles
  -> ObstructionSoundness
```

No `MINLIB` extraction is composed in Stage 2. That is reserved for Stage 3.

## 10. Genericity

Public theorem assumptions:

```lean
{Voter : Type u}
{Alt : Type v}
[DecidableEq Alt]
[Fintype Alt]
```

No public theorem requires:

- `Voter = Fin n`;
- `Alt = Fin m`;
- `[Fintype Voter]`;
- `[DecidableEq Voter]`.

Generic voter equality inside `twoRankingProfile` is handled locally with `classical`.

## 11. Non-Circularity

No final theorem dependency:

- `sen_impossibility_lifts` is not imported or used.

No BaseCase theorem dependency:

- `SocialChoiceAtlas.Sen.BaseCase24.Theorem` is not imported or used.

No legacy private lemma dependency:

- `sen_lift_case_*` lemmas are not imported or used.

Dependency scan results:

- Matches appeared only in module docstrings explaining non-dependence on `ImpossibilityLift.lean` and future Stage 3 refactoring.
- No import or proof dependency matched the forbidden theorem/module names.

## 12. Non-Claims

Stage 2 does not claim:

- `MINLIB -> ¬ SocialAcyclic` composition;
- final finite-obstruction bridge completion;
- refactoring of `sen_impossibility_lifts`;
- literal two-voter subinstance;
- literal Sen24 subinstance transport;
- CNF/LRAT/atlas transport;
- repair/MCS transfer;
- manuscript claim update.

## 13. Validation

Standalone builds:

- `lake env lean SocialChoiceAtlas/Sen/ObstructionProfiles.lean`: passed.
- `lake env lean SocialChoiceAtlas/Sen/ObstructionSoundness.lean`: passed.
- `lake build SocialChoiceAtlas.Sen.ObstructionSoundness`: passed.

Existing M2 smoke:

- `./scripts/ci_m2_smoke.sh`: passed.

Forbidden-token scan:

```text
grep -RInE '\b(sorry|admit|axiom|unsafe)\b|aesop\?|exact\?' \
  SocialChoiceAtlas/Sen/ObstructionProfiles.lean \
  SocialChoiceAtlas/Sen/ObstructionSoundness.lean
```

Result: no matches.

Dependency scan:

```text
grep -RInE \
  'ImpossibilityLift|BaseCase24\.Theorem|sen_impossibility_lifts|sen_impossibility_basecase|sen_lift_case_' \
  SocialChoiceAtlas/Sen/ObstructionProfiles.lean \
  SocialChoiceAtlas/Sen/ObstructionSoundness.lean
```

Result: docstring-only matches for `ImpossibilityLift.lean` / `sen_impossibility_lifts`; no proof dependency.

Axiom audit:

```text
SenOutcomeObstruction.refutes_socialAcyclic: [propext, Quot.sound]
outcome_of_twoOverlap: [propext, Classical.choice, Quot.sound]
outcome_of_zOnly: [propext, Classical.choice, Quot.sound]
outcome_of_wOnly: [propext, Classical.choice, Quot.sound]
outcome_of_disjoint: [propext, Classical.choice, Quot.sound]
outcome_of_classifiedWitness: [propext, Classical.choice, Quot.sound]
classifiedWitness_not_socialAcyclic: [propext, Classical.choice, Quot.sound]
```

No custom axiom or `sorryAx` appeared.

`git diff --check`: passed.

## 14. Stage 2 Verdict

**PASS.**

PASS criteria status:

1. Generic prefix-ranking construction compiles: passed.
2. Generic two-ranking ambient profile compiles: passed.
3. Public theorems do not depend on `Fin n` / `Fin m`: passed.
4. `SenOutcomeObstruction` distinguishes three outcomes: passed.
5. Outcome refutation theorem holds: passed.
6. O2 strict conflict construction holds: passed.
7. zOnly 3-cycle construction holds: passed.
8. wOnly reuses orientation symmetry: passed.
9. Disjoint 4-cycle construction holds: passed.
10. Raw shape dispatcher holds: passed.
11. Classified witness flagship holds: passed.
12. Classified witness refutes `SocialAcyclic`: passed.
13. Exact O2/O3/O4 support cardinalities hold: passed.
14. Final Sen theorem is not used: passed.
15. Existing M2 smoke passes: passed.
16. No placeholders: passed.
17. Protected files unchanged: passed.

## 15. Stage 3 Readiness

Stage 3 should add the public composition theorem:

```lean
theorem sen_impossibility_from_obstruction_basis
    (F : SWF Voter Alt)
    (hUN : UN F)
    (hMINLIB : MINLIB F) :
    ¬ SocialAcyclic F
```

Expected composition:

```text
exists_classified_senRightsWitness
  -> outcome_of_classifiedWitness
  -> SenOutcomeObstruction.refutes_socialAcyclic
```

Then `sen_impossibility_lifts` can be refactored as a corollary in a later commit, without changing its statement.

Legacy helper strategy:

- move or re-export the ranking/profile helpers from `ObstructionProfiles`;
- replace duplicated helper code in `ImpossibilityLift.lean` only after the obstruction theorem is complete;
- keep the base-case module untouched until the generic core is stable.

Root import and CI plan:

- add `ObstructionBasis`, `ObstructionProfiles`, and `ObstructionSoundness` to the root import only after Stage 3;
- extend `scripts/ci_m2_smoke.sh` after Stage 3 to check the final obstruction theorem names.

Manuscript updates remain gated until Stage 3 completes the `MINLIB -> classified witness -> outcome obstruction -> ¬ SocialAcyclic` composition.
