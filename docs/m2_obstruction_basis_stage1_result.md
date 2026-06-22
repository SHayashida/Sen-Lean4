# M2 Obstruction Basis Stage 1 Result

## 1. Baseline

- Branch: `codex/m2-obstruction-basis-stage1`
- Starting HEAD: `1e42884605bc9d4ef1c06f7f004a4697025b6aa8`
- `origin/main`: `73c891fa3edd96148238570f16453c484fccf283`
- `origin/main` latest: `73c891f Merge pull request #9 from SHayashida/codex/m2.1-candidate-b`
- Precheck document status: already tracked in starting HEAD.

## 2. Files

Created:

- `SocialChoiceAtlas/Sen/ObstructionBasis.lean`
- `docs/m2_obstruction_basis_stage1_result.md`

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

## 3. Implemented Public Interface

New module:

```lean
SocialChoiceAtlas.Sen.ObstructionBasis
```

Public structures:

- `SenRightsWitness`
- `ClassifiedSenRightsWitness`

Public inductives:

- `SenRawOverlapShape`
- `SenObstructionShape`

Public definitions:

- `SenRightsWitness.support`
- `SenRawOverlapShape.kind`
- `classify_raw_overlap`
- `ClassifiedSenRightsWitness.kind`
- `ClassifiedSenRightsWitness.support`

Public theorems:

- `SenRightsWitness.support_card_le_four`
- `exists_senRightsWitness`
- `ClassifiedSenRightsWitness.support_card_le_four`
- `exists_classified_senRightsWitness`

No root import was added. The module was built standalone.

## 4. Genericity

The Stage 1 interface is generic over:

```lean
{Voter : Type u}
{Alt : Type v}
[DecidableEq Alt]
[Fintype Alt]
```

No `DecidableEq Voter` assumption is required. No `Fintype Voter` assumption is required. No `Fin n` or `Fin m` specialization remains in the Stage 1 objects.

The alternative type retains `[DecidableEq Alt] [Fintype Alt]` because the repository's `SWF`, `Profile`, and `Ranking` definitions are stated for finite alternatives with decidable equality.

## 5. Extraction

`exists_senRightsWitness` maps `MINLIB F` directly to the public witness package:

```lean
theorem exists_senRightsWitness
    (F : SWF Voter Alt) (hMINLIB : MINLIB F) :
    Nonempty (SenRightsWitness F)
```

The proof only destructs the nested existential in `MINLIB`. It does not use `sen_impossibility_lifts`, the base-case theorem, or any acyclicity conclusion.

The witness preserves the original `MINLIB` field order and meaning:

- rights holders `i`, `j`;
- proof `i_ne_j`;
- decisive pair `(x, y)` for `i`;
- decisive pair `(z, w)` for `j`;
- proofs `x_ne_y`, `z_ne_w`;
- decisiveness proofs for both ordered pairs.

No all-distinctness or disjointness assumption is added.

## 6. Classification

The raw classifier mirrors the current proof dispatcher:

```text
z in {x,y},  w in {x,y}   -> twoOverlap
z in {x,y},  w notin {x,y} -> zOnly
z notin {x,y}, w in {x,y}  -> wOnly
z notin {x,y}, w notin {x,y} -> disjoint
```

Each `SenRawOverlapShape` constructor stores its branch proofs, so Stage 2 does not need to repeat the same membership split.

The data-valued classifier is:

```lean
def classify_raw_overlap
    (wit : SenRightsWitness F) :
    SenRawOverlapShape wit.x wit.y wit.z wit.w
```

The canonical paper-facing map is:

```lean
def SenRawOverlapShape.kind :
    SenRawOverlapShape x y z w -> SenObstructionShape
```

Mapping:

- `twoOverlap -> O2`
- `zOnly -> O3`
- `wOnly -> O3`
- `disjoint -> O4`

`exists_classified_senRightsWitness` is the Stage 1 flagship:

```lean
theorem exists_classified_senRightsWitness
    (F : SWF Voter Alt) (hMINLIB : MINLIB F) :
    Nonempty (ClassifiedSenRightsWitness F)
```

## 7. Support Bound

The distinguished alternative support is:

```lean
def SenRightsWitness.support (wit : SenRightsWitness F) : Finset Alt :=
  {wit.x, wit.y, wit.z, wit.w}
```

Kernel-checked bound:

```lean
theorem SenRightsWitness.support_card_le_four
    (wit : SenRightsWitness F) :
    wit.support.card <= 4
```

The classified package inherits the same bound:

```lean
theorem ClassifiedSenRightsWitness.support_card_le_four
    (cw : ClassifiedSenRightsWitness F) :
    cw.support.card <= 4
```

Exact shape cardinalities were not proved in Stage 1. They are suitable for Stage 1.1 or Stage 2:

- `twoOverlap -> support.card = 2`
- `zOnly / wOnly -> support.card = 3`
- `disjoint -> support.card = 4`

## 8. Non-Claims

Stage 1 does not claim:

- a literal two-voter restriction theorem;
- a literal two-voter Sen24 subinstance inside every general instance;
- Sen24 atlas transport;
- CNF/LRAT lift;
- shape soundness;
- `strictConflict`, `cycle3`, or `cycle4` construction;
- reconstruction of `sen_impossibility_lifts` as a corollary;
- repair or MCS transfer;
- completion of a finite obstruction basis theorem.

Safe wording after Stage 1:

> A generic bounded witness ontology and exhaustive O2/O3/O4 overlap classification are kernel-checked.

## 9. Stage 1 Verdict

**PASS.**

PASS criteria status:

1. Generic `SenRightsWitness` is public: passed.
2. `MINLIB` extraction is public: passed.
3. Raw four-way overlap classification is exhaustive: passed.
4. O2/O3/O4 canonicalization exists: passed.
5. `support.card <= 4` is proved: passed.
6. Module compiles standalone: passed.
7. Existing M2 smoke passes: passed.
8. Existing M2 theorem, paper, and scope wall unchanged: passed.
9. No circular import: passed.
10. No placeholders or prohibited proof-search stubs: passed.

## 10. Stage 2 Readiness

Existing private lemmas that can be refactored in Stage 2:

- `sen_lift_case_two_overlap`
- `sen_lift_case_one_overlap_shared_x`
- `sen_lift_case_one_overlap_shared_y`
- `sen_lift_case_one_overlap_z_in`
- `sen_lift_case_one_overlap_w_in`
- `sen_lift_case_disjoint`

Required generic helpers:

- a generic profile lift over arbitrary `Voter`, not only `Fin n`;
- reuse or relocation of `rankingOfPrefix` helpers from `ImpossibilityLift.lean`;
- outcome-obstruction datatype for strict conflict / 3-cycle / 4-cycle.

Expected Stage 2 theorem interfaces:

```lean
inductive SenOutcomeObstruction (F : SWF Voter Alt) : Prop
  | strictConflict ...
  | cycle3 ...
  | cycle4 ...

theorem obstruction_of_classified_witness
    (hUN : UN F)
    (cw : ClassifiedSenRightsWitness F) :
    SenOutcomeObstruction F

theorem sen_obstruction_refutes_acyclicity
    (o : SenOutcomeObstruction F) :
    ¬ SocialAcyclic F
```

Principal risks:

- accidentally depending on `sen_impossibility_lifts`;
- exposing private implementation lemmas without a clean public outcome interface;
- overclaiming literal subinstance transport;
- increasing imports too early;
- accidentally weakening the M2 scope wall.
