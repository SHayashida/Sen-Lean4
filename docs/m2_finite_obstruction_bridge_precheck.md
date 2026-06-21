# M2 Finite-Obstruction Bridge Precheck

## 1. Executive Verdict

**Verdict: CONDITIONAL GO.**

M2 can plausibly be upgraded from a proof-pattern lift to a **bounded semantic obstruction theorem**: the existing proof already destructs `MINLIB` into two rights holders and two decisive pairs, classifies the pair overlap into two-overlap / one-overlap / disjoint, and derives an asymmetry conflict, 3-cycle, or 4-cycle. However, the current code is still Level 0 proof-pattern reuse: the obstruction data, shape classification, and outcome obstruction are not public reusable interfaces, and the shape-specific soundness lemmas are private implementation details. A Level 1 theorem is strongly feasible, and a Level 2 finite canonical shape theorem is feasible with a focused refactor; Level 3 literal finite subinstance and Level 4 CNF/artifact bridge are not supported by current evidence.

The recommended paper-level name after implementation is **bounded semantic obstruction theorem** or **finite witness-pattern classification**. Do not use **finite-atlas bridge**. Use **finite semantic obstruction basis** only after T1-T4 and canonical adequacy are implemented as independent public interfaces.

## 2. Repository Baseline

Baseline commands requested:

```text
git status --short
git branch --show-current
git fetch origin
git rev-parse HEAD
git rev-parse origin/main
git log -1 --oneline origin/main
```

Observed baseline:

- Initial branch before task branch creation: `codex/m3-paper-scaffold`.
- Initial `HEAD`: `08a296b5d2a9fa8ad0769a451cf6b20a23f5069f`.
- Initial `origin/main`: `73c891fa3edd96148238570f16453c484fccf283`.
- Initial working tree before branch switch: clean.
- `git fetch origin` succeeded after elevated permission was required to write `.git/FETCH_HEAD`.
- Current task branch: `codex/m2-finite-obstruction-precheck`.
- Current `HEAD`: `73c891fa3edd96148238570f16453c484fccf283`.
- Current `origin/main`: `73c891fa3edd96148238570f16453c484fccf283`.
- `origin/main` latest commit: `73c891f Merge pull request #9 from SHayashida/codex/m2.1-candidate-b`.
- After switching to `origin/main`, unrelated untracked directories `papers/m2_1/` and `papers/m3/` were visible and left untouched.

Inspected files:

- `SocialChoiceAtlas/Axioms/Liberalism.lean`
- `SocialChoiceAtlas/Axioms/Pareto.lean`
- `SocialChoiceAtlas/Axioms/Rationality.lean`
- `SocialChoiceAtlas/Core/Basics.lean`
- `SocialChoiceAtlas/Core/Ranking.lean`
- `SocialChoiceAtlas/Core/Profile.lean`
- `SocialChoiceAtlas/Sen/BaseCase24/Spec.lean`
- `SocialChoiceAtlas/Sen/BaseCase24/Theorem.lean`
- `SocialChoiceAtlas/Sen/Lifting/ImpossibilityLift.lean`
- `papers/m2/CLAIM_BOUNDARY.md`
- `papers/m2/README.md`
- `papers/m2/sections/01_intro.tex`
- `papers/m2/sections/03b_contributions.tex`
- `papers/m2/sections/04_results_plan.tex`
- `docs/m2_scope_wall.md`
- `docs/gates/m2/aim_signoff.md`
- `docs/gates/m2/impossibility_lift_stage1_plan.md`
- `scripts/ci_m2_smoke.sh`
- `SocialChoiceAtlas.lean`
- `lakefile.lean`

## 3. Current M2 Architecture

### Actual origin of `sen_impossibility_lifts`

`SocialChoiceAtlas/Sen/Lifting/ImpossibilityLift.lean` does **not** import `SocialChoiceAtlas.Sen.BaseCase24.Theorem`. It imports only Mathlib plus the generic core and axiom modules:

```text
SocialChoiceAtlas.Core.Basics
SocialChoiceAtlas.Core.Ranking
SocialChoiceAtlas.Core.Profile
SocialChoiceAtlas.Axioms.Pareto
SocialChoiceAtlas.Axioms.Liberalism
SocialChoiceAtlas.Axioms.Rationality
```

Thus, `sen_impossibility_lifts` does not use `sen_impossibility_basecase` as a theorem, does not reuse a base-case theorem by embedding/restriction, and does not transport the Sen24 CNF artifact. It directly re-proves the base-case case split over `(Fin n, Fin m)`.

Classification:

- A. **Proof-pattern reuse:** yes. This is the current M2 architecture.
- B. **Semantic obstruction extraction:** partially implicit only. `hMINLIB` is destructed, but no public obstruction object is produced.
- C. **Finite-atlas-to-family theorem transport:** no. The CNF atlas and LRAT artifacts are not formal inputs.

The current proof branches are private implementation details, not public theorem interfaces.

### Current dependency graph

```text
MINLIB
  -> witness extraction
two decisive voters + two decisive pairs
  -> overlap case split
two-overlap / one-overlap / disjoint
  ->
asymmetry conflict / cycle3 / cycle4
  ->
not SocialAcyclic
```

Implementation inventory:

| Step | Current path and name | Status |
|---|---|---|
| `MINLIB -> witnesses` | `SocialChoiceAtlas/Sen/Lifting/ImpossibilityLift.lean`, theorem `sen_impossibility_lifts`, `rcases hMINLIB` | inline in final theorem |
| witness extraction in base case | `SocialChoiceAtlas/Sen/BaseCase24/Theorem.lean`, structure `MINLIBWitness`, def `extractWitness` | base-case local, not reused |
| overlap case split | `sen_impossibility_lifts`, `by_cases hz`, `by_cases hw` | inline dispatcher |
| two-overlap soundness | private lemma `sen_lift_case_two_overlap` | private |
| one-overlap soundness | private lemmas `sen_lift_case_one_overlap_shared_x`, `sen_lift_case_one_overlap_shared_y`, dispatchers `sen_lift_case_one_overlap_z_in`, `sen_lift_case_one_overlap_w_in` | private |
| disjoint soundness | private lemma `sen_lift_case_disjoint` | private |
| 3-cycle refutation | `SocialChoiceAtlas/Core/Basics.lean`, theorem `cycle3_implies_not_acyclic` | public |
| 4-cycle refutation | `SocialChoiceAtlas/Core/Basics.lean`, theorem `cycle4_implies_not_acyclic` | public |
| two-overlap conflict | `SocialChoiceAtlas/Core/Basics.lean`, theorem `strictPart_asymm` | public |

Public helpers in `ImpossibilityLift.lean`:

- `exists_not_mem_of_card_lt`
- `four_le_card_fin`
- `rankingOfPrefix`
- `rankingOfPrefix_position_of_mem_prefix`
- `rankingOfPrefix_prefers_of_indexOf_lt`
- `rankingOfPrefix_position_getElem`
- `rankingOfPrefix_prefers_getElem`
- `ranking4Prefix`
- `ranking4Prefix_prefers_of_lt`
- `liftProfile`
- `liftProfile_apply_j`
- `liftProfile_apply_ne`
- `prefers_i_liftProfile_at_j`
- `prefers_i_liftProfile_at_other`
- `prefers_i_liftProfile_at_i`
- `liftProfile_unanimous`
- `sen_impossibility_lifts`

Private helpers in `ImpossibilityLift.lean`:

- `extendList`
- `extendList_nodup`
- `extendList_complete`
- `rankingOfPrefix_toList`
- all `sen_lift_case_*` soundness lemmas

### Non-dependence of current hypotheses

- `_hn : 2 <= n` is not used because `MINLIB` already supplies `i j : Fin n` with `i != j`.
- `_hm : 4 <= m` is not used because the proof never needs to manufacture four fresh alternatives. The needed alternatives are among `x, y, z, w`, and overlap cases use two or three of them.
- `MINLIB` supplies exactly: two distinct voters, a nondegenerate decisive pair for the first voter, and a nondegenerate decisive pair for the second voter.
- The current theorem is stated for `Fin n` and `Fin m`, but the proof content is not intrinsically tied to `Fin n`. It uses arbitrary chosen voters from `MINLIB` and a profile with at most two ranking values.
- The alternative type needs `[DecidableEq Alt] [Fintype Alt]` because `Ranking Alt` is list-complete over a finite type. The voter type does not need to be finite for the semantic proof; equality on voters can be handled classically in profile construction.

The following stronger generic signature is feasible as the honest semantic target:

```lean
theorem sen_impossibility_general
    {Voter Alt : Type*}
    [DecidableEq Alt]
    [Fintype Alt]
    (F : SWF Voter Alt)
    (hUN : UN F)
    (hMINLIB : MINLIB F) :
    ¬ SocialAcyclic F
```

If public profile helpers are made computable/simp-friendly, adding `[DecidableEq Voter]` may be convenient. It is not mathematically essential if the proof uses `classical` inside noncomputable profile construction.

## 4. Candidate Meanings of Finite Obstruction

| Level | Meaning | Current status | Precheck verdict |
|---|---|---|---|
| Level 0 | Proof-pattern reuse | Implemented by `sen_impossibility_lifts` | Already present, not enough for upgrade |
| Level 1 | Bounded semantic witness classification | Type-feasible; currently implicit | CONDITIONAL GO |
| Level 2 | Canonical obstruction normal form | Feasible with O2/O3/O4 shape packaging and orientation normalization | CONDITIONAL GO, requires implementation |
| Level 3 | Literal finite subinstance bridge | Not established | NO-GO |
| Level 4 | CNF / artifact bridge | Explicitly outside M2 scope wall | NO-GO |

Level 1 and Level 2 are the safe target. Level 3 would require a restriction operator for arbitrary `F`, preservation of outcomes after removing voters/alternatives, and preservation of `UN`, `MINLIB`, and `SocialAcyclic` under restriction. None of that exists in current M2.

## 5. Strongest Honest Theorem

Mathematical statement:

> From any semantic `UN + MINLIB` instance, extract two distinguished rights holders, two decisive ordered pairs, and at most four distinguished alternatives. The overlap shape of the two decisive pairs is one of three finite cases. Each case soundly produces either a strict-part asymmetry conflict, a 3-cycle, or a 4-cycle at a profile using at most two ranking types. Therefore `SocialAcyclic` is refuted.

Lean pseudo-signature:

```lean
structure SenRightsWitness (F : SWF Voter Alt) where
  voter_i voter_j : Voter
  voters_ne : voter_i ≠ voter_j
  x y z w : Alt
  x_ne_y : x ≠ y
  z_ne_w : z ≠ w
  dec_i : Decisive F voter_i x y
  dec_j : Decisive F voter_j z w

inductive SenOverlapKind
  | twoOverlap
  | oneOverlap
  | disjoint

inductive SenOutcomeObstruction (F : SWF Voter Alt) : Prop
  | strictConflict (p : Profile Voter Alt) (x y : Alt) :
      strictPart (F p) x y -> strictPart (F p) y x -> SenOutcomeObstruction F
  | cycle3 (p : Profile Voter Alt) :
      cycle3 (strictPart (F p)) -> SenOutcomeObstruction F
  | cycle4 (p : Profile Voter Alt) :
      cycle4 (strictPart (F p)) -> SenOutcomeObstruction F

theorem extract_sen_rights_witness
    (hMINLIB : MINLIB F) :
    Nonempty (SenRightsWitness F)

theorem classify_sen_rights_witness
    (w : SenRightsWitness F) :
    ClassifiedSenWitness F

theorem sen_obstruction_of_classified_witness
    (hUN : UN F)
    (cw : ClassifiedSenWitness F) :
    SenOutcomeObstruction F

theorem sen_obstruction_refutes_acyclicity
    (o : SenOutcomeObstruction F) :
    ¬ SocialAcyclic F

theorem sen_impossibility_from_bounded_obstruction
    {Voter Alt : Type*} [DecidableEq Alt] [Fintype Alt]
    (F : SWF Voter Alt)
    (hUN : UN F)
    (hMINLIB : MINLIB F) :
    ¬ SocialAcyclic F
```

Exact assumptions:

- Required: `[DecidableEq Alt] [Fintype Alt]`.
- Not required mathematically: `Fintype Voter`, `Fin n`, `Fin m`, explicit `2 <= n`, explicit `4 <= m`.
- Possibly useful for public helper simp lemmas: `[DecidableEq Voter]`, unless helpers are noncomputable and use `classical`.

Exact conclusion:

- `¬ SocialAcyclic F`, not merely `¬ no_cycle3` or `¬ no_cycle4`.
- No claim about CNF/LRAT, solver certificates, or repair transfer.

## 6. Candidate Obstruction Ontology

### Option A: overlap-shape centered

This is close to current code and should be the first extraction layer.

```lean
inductive SenOverlapKind
  | twoOverlap
  | oneOverlap
  | disjoint

structure SenRightsWitness (F : SWF Voter Alt) where
  voter_i voter_j : Voter
  voters_ne : voter_i ≠ voter_j
  x y z w : Alt
  x_ne_y : x ≠ y
  z_ne_w : z ≠ w
  dec_i : Decisive F voter_i x y
  dec_j : Decisive F voter_j z w

structure ClassifiedSenWitness (F : SWF Voter Alt) where
  witness : SenRightsWitness F
  kind : SenOverlapKind
  shape_proof : ...
```

This gives the right bounded support claim: two voters, two decisive pairs, and at most four alternatives.

### Option B: outcome-obstruction centered

This is the best final refutation interface.

```lean
inductive SenOutcomeObstruction (F : SWF Voter Alt) : Prop
  | strictConflict (p : Profile Voter Alt) (x y : Alt) :
      strictPart (F p) x y -> strictPart (F p) y x -> SenOutcomeObstruction F
  | cycle3 (p : Profile Voter Alt) :
      cycle3 (strictPart (F p)) -> SenOutcomeObstruction F
  | cycle4 (p : Profile Voter Alt) :
      cycle4 (strictPart (F p)) -> SenOutcomeObstruction F
```

The two-overlap case does not naturally produce a cycle before contradiction; representing it as `strictConflict` avoids forcing a fake cycle ontology.

### Option C: two-stage shape and outcome

Recommended architecture:

```text
rights witness
  -> overlap classification
  -> canonical profile construction
  -> outcome obstruction
  -> not acyclic
```

Option C is the cleanest bridge: Option A supplies finite canonicality, Option B supplies uniform refutation.

Support bounds:

- Voters: exactly two distinguished rights holders.
- Alternatives: at most four distinguished alternatives, possibly only two or three after overlap.
- Ranking patterns: at most two ranking types in the constructed profile.
- Ambient voters and alternatives remain present.

## 7. Theorem Factorization

### T1. MINLIB witness extraction

Feasible and essentially definitional:

```lean
theorem extract_sen_rights_witness
    (hMINLIB : MINLIB F) :
    Nonempty (SenRightsWitness F)
```

Scratch status: typechecked in `/tmp/m2_bridge_precheck_scratch.lean`.

### T2. Exhaustive shape classification

Feasible:

```lean
theorem classify_sen_rights_witness
    (w : SenRightsWitness F) :
    ClassifiedSenWitness F
```

The core proof is a case split on whether `z` and `w` are equal to `x` or `y`. The scratch file typechecked a propositional exhaustive classifier:

```lean
hasTwoOverlap w ∨ hasOneOverlap w ∨ hasDisjoint w
```

Orientation normalization should use `Decisive.symm` where `w` rather than `z` is the shared point.

### T3. Shape soundness

Feasible but nontrivial. The existing private lemmas already contain the proof content:

- `sen_lift_case_two_overlap`
- `sen_lift_case_one_overlap_shared_x`
- `sen_lift_case_one_overlap_shared_y`
- `sen_lift_case_one_overlap_z_in`
- `sen_lift_case_one_overlap_w_in`
- `sen_lift_case_disjoint`

They need to be moved behind a public interface returning `SenOutcomeObstruction F`, not `¬ SocialAcyclic F` directly.

### T4. Obstruction refutation

Feasible:

```lean
theorem sen_obstruction_refutes_acyclicity
    (o : SenOutcomeObstruction F) :
    ¬ SocialAcyclic F
```

Implementation routes:

- `strictConflict`: use `strictPart_asymm`.
- `cycle3`: use `cycle3_implies_not_acyclic`.
- `cycle4`: use `cycle4_implies_not_acyclic`.

### T5. General bridge theorem

Feasible only if implemented as T1 -> T2 -> T3 -> T4 composition. It must not be defined as a one-line call to `sen_impossibility_lifts`.

Recommended theorem name:

```lean
theorem sen_impossibility_from_bounded_obstruction
```

If later used to recover the existing theorem:

```lean
theorem sen_impossibility_lifts ... := by
  exact sen_impossibility_from_bounded_obstruction F hUN hMINLIB
```

### T6. Canonical basis adequacy

Feasible in the weak, combinatorial sense:

> Every `MINLIB` contradiction witness falls into O2, O3, or O4 up to voter naming, decisive-pair orientation, and unused-alternative padding.

Not currently feasible in the strong semantic-transport sense:

> Every general SWF transports to a literal Sen24 SWF subinstance.

That stronger claim would require restriction/preservation theorems not present in the repo.

### Dependency DAG and cycle check

```text
Core/Axioms
  -> ObstructionBasis
      T1 extraction
      T2 classification
      T3 shape soundness
      T4 obstruction refutation
      T5 generic theorem
  -> Lifting/ImpossibilityLift as corollary
  -> BaseCase24/Theorem optionally as corollary or comparison
```

No theorem in T1-T4 should import or depend on `sen_impossibility_lifts` or `sen_impossibility_basecase`.

## 8. Sen24 Connection

### 8.1 Base-case proof code sharing

Possible with a refactor, but not currently true. A new module such as:

```text
SocialChoiceAtlas/Sen/ObstructionBasis.lean
```

should import only core and axioms. Then both:

```text
SocialChoiceAtlas/Sen/BaseCase24/Theorem.lean
SocialChoiceAtlas/Sen/Lifting/ImpossibilityLift.lean
```

can become corollaries or specialized wrappers. This avoids importing BaseCase into the generic module and prevents an import cycle.

### 8.2 Semantic pattern normal form

O2/O3/O4 correspond to the three Sen24 proof patterns:

- O2: same unordered pair / two-overlap -> strict conflict.
- O3: exactly one shared alternative -> 3-cycle.
- O4: disjoint decisive pairs -> 4-cycle.

Required normalizations:

- voter renaming;
- alternative renaming;
- decisive-pair orientation normalization via `Decisive.symm`;
- ranking completion / padding for unused alternatives.

This is a semantic pattern correspondence, not a CNF or atlas correspondence.

### 8.3 Artifact non-transfer

The following do not transfer from this semantic bridge:

- lever masks;
- CNF clauses;
- LRAT certificate;
- `no_cycle3` / `no_cycle4` audit;
- MCS / repair family;
- finite atlas status table.

This remains governed by `docs/m2_scope_wall.md`.

## 9. Restriction vs Ambient Witness

The current proof is **not** a literal two-voter restriction theorem.

`liftProfile` assigns voter `j` ranking `r_j` and every other voter ranking `r_i`. Therefore:

- decisive edges use two distinguished voters;
- `UN` edges use all voters, but all non-`j` voters have the same ranking type as voter `i`;
- the proof uses at most two ranking types, not only two voters;
- arbitrary extra voters remain in the ambient SWF;
- arbitrary extra alternatives remain in the ambient alternative type and are completed in the ranking tail.

Safe wording:

> The contradiction is supported by two distinguished rights holders, at most four distinguished alternatives, and a profile using at most two ranking types.

Forbidden wording:

> Every general Sen instance contains a two-voter Sen24 subinstance.

Also forbidden:

> The Sen24 CNF certificate lifts to arbitrary finite instances.

To prove a literal subinstance bridge, one would need:

- a voter restriction operator for arbitrary `SWF`;
- an alternative restriction operator for arbitrary `SWF`;
- outcome preservation for the restricted SWF;
- `UN`, `MINLIB`, and `SocialAcyclic` preservation theorems;
- proof that extra voters do not affect social outcomes after restriction.

No such interface exists now.

## 10. Formalization Feasibility

Reusable existing lemmas:

- `Decisive.symm`
- `strictPart_asymm`
- `cycle3_implies_not_acyclic`
- `cycle4_implies_not_acyclic`
- `rankingOfPrefix`
- `rankingOfPrefix_prefers_getElem`
- `liftProfile_unanimous`

Required refactors:

- expose a public `SenRightsWitness` structure;
- expose public overlap-kind and classified-witness objects;
- refactor private `sen_lift_case_*` lemmas to return `SenOutcomeObstruction`;
- generalize `liftProfile` from `Fin n` to arbitrary `Voter`, or keep the existing helper as a corollary of a generic helper;
- generalize shape soundness from `Fin m` to arbitrary finite `Alt`;
- keep existing `sen_impossibility_lifts` as a corollary rather than a parallel proof.

Import structure:

```text
SocialChoiceAtlas/Sen/ObstructionBasis.lean
  imports Core + Axioms only

SocialChoiceAtlas/Sen/Lifting/ImpossibilityLift.lean
  imports ObstructionBasis

SocialChoiceAtlas/Sen/BaseCase24/Theorem.lean
  may later import ObstructionBasis if base-case refactor is desired
```

Estimated proof obligations:

- extraction: trivial;
- classification: small finite equality case split over `z,w` membership in `{x,y}`;
- profile/ranking helpers: mostly already available;
- soundness refactor: medium, because existing private lemmas conclude `¬ SocialAcyclic F` and must be split into "construct obstruction" plus "refute";
- base-case common-core refactor: optional and potentially high churn.

Principal risks:

- accidental circular proof if T5 calls the existing impossibility theorem;
- overclaiming Level 3 literal restriction;
- public API churn if private lemmas are exposed too directly;
- proof-term bloat from generalized profile/ranking helpers;
- manuscript drift toward CNF/artifact transfer language.

Scratch Lean check:

```text
lake env lean /tmp/m2_bridge_precheck_scratch.lean
```

Result: passed after renaming dependent structure fields one per line. The scratch file typechecked generic `SenRightsWitness`, `SenOverlapKind`, propositional shape classification, `SenOutcomeObstruction`, `extract_sen_rights_witness`, and a generic non-`Fin n` profile lift. The scratch file used no `sorry`, `admit`, `aesop?`, or `exact?` and was removed after the check.

## 11. Novelty Test

This is more than a pure rename if and only if T1-T4 are implemented as reusable public theorem interfaces. In that form, downstream code can consume:

- a rights witness;
- a finite shape classification;
- an outcome obstruction;
- a uniform refutation theorem.

That would strengthen the M2 manuscript from "the proof pattern lifts" to "the semantic obstruction structure has a finite bounded classification." It would not establish a new solver artifact, new repair theorem, or finite-atlas transport theorem.

External literature novelty is **not assessed** in this precheck. The report only evaluates repository-local formal feasibility and claim safety.

## 12. Scope-Wall Preservation

The bridge must not lift CNF/LRAT:

- no claim that `Certificates/sen24.cnf` generalizes;
- no claim that `Certificates/sen24.lrat` generalizes;
- no claim that `Certificates/atlas/case_11111/**` generalizes;
- no solver experiment is needed for this semantic bridge.

The `no_cycle3` / `no_cycle4` limitation remains:

- the Lean theorem reaches full `SocialAcyclic`;
- the CNF Witness/Audit layer remains short-cycle scoped;
- `no_cycle3 ∧ no_cycle4` is not a family-level acyclicity encoding for `m >= 5`.

Repair transfer must not be claimed:

- no MCS transfer theorem;
- no family-level repair canonicality theorem;
- no finite-atlas repair basis.

## 13. Implementation Plan if GO

Proposed new file:

```text
SocialChoiceAtlas/Sen/ObstructionBasis.lean
```

Alternative if locality under M2 is preferred:

```text
SocialChoiceAtlas/Sen/Lifting/ObstructionBasis.lean
```

Recommended order:

1. Commit 1: obstruction data types, extraction theorem, and exhaustive shape classification.
2. Commit 2: generic profile/ranking helpers, including arbitrary-voter `genericLiftProfile`.
3. Commit 3: shape-specific soundness theorems returning `SenOutcomeObstruction`.
4. Commit 4: obstruction-refutation theorem and `sen_impossibility_from_bounded_obstruction`.
5. Commit 5: make `sen_impossibility_lifts` a corollary.
6. Commit 6: optionally refactor `BaseCase24/Theorem.lean` to share the semantic core.
7. Commit 7: update CI, claim boundary, and M2 manuscript wording.

Base-case refactor is valuable but not required for the initial bridge. It should be delayed if it risks touching protected base-case proof files too early.

CI changes:

- add the new module to `SocialChoiceAtlas.lean` only after it is proof-complete;
- extend `scripts/ci_m2_smoke.sh` to grep for the new theorem names;
- keep the no-placeholder grep.

Manuscript changes:

- replace "polymorphic port" as the strongest result only after the theorem interfaces exist;
- use "bounded semantic obstruction theorem" unless canonical basis adequacy is proved;
- keep the CNF scope wall unchanged.

## 14. Kill Switches

Stop the upgrade if any of these are discovered:

- T1 or T2 is obtained by calling `sen_impossibility_lifts` backward.
- Shape soundness cannot be factored without duplicating most of the current proof in a non-reusable way.
- The proposed generic theorem requires hidden `Fin n`/`Fin m` properties after all.
- Public theorem interfaces create an import cycle with `BaseCase24`.
- The only deliverable is a rename of private lemmas.
- Any manuscript wording starts implying literal two-voter restriction.
- Any manuscript wording implies CNF/LRAT/atlas transfer.
- `ci_m2_smoke` or default build cost becomes unacceptable.

## 15. Final Recommendation

This can be used as an Arrow-free doctoral bridge only if named conservatively and implemented as an independent semantic interface. The correct near-term name is:

```text
bounded semantic obstruction theorem
```

or:

```text
finite witness-pattern classification
```

After T1-T4 and canonical adequacy are complete, the stronger phrase:

```text
finite semantic obstruction basis
```

may be acceptable, where "basis" means a complete finite generating family of semantic contradiction shapes, not a minimal or irredundant basis.

Current M2 should not yet be described as a finite-obstruction bridge theory. Today it remains a Proof-layer transfer theorem with an artifact scope wall. The upgrade is feasible, but only as a new public factorization that separates extraction, finite shape classification, shape soundness, and obstruction refutation.
