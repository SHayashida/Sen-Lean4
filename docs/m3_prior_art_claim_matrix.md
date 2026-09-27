> Status: research-note freeze for M3 prior-art and contribution boundaries
>
> Scope: literature positioning and repository claim discipline
>
> Not a theorem
>
> Not a manuscript claim by itself
>
> Not evidence that absence in the surveyed literature is universal

# M3 prior-art claim matrix and contribution boundary

## Purpose and authority

This note freezes the paper-facing M3 literature comparison and binds it to
the theorem boundary implemented in the current Lean source. Its purpose is to
distinguish:

1. established substrate and prior art;
2. theorem results currently checked by the Lean kernel in M3;
3. current artifact evidence;
4. proposed future theoretical strengthenings; and
5. proposed future system and assurance contributions.

The Lean files under `SocialChoiceAtlas/Reportability/` are authoritative for
current theorem statements. The matrix below is the authoritative research-note
input for the seven reviewed works and eight axes; it is not an exhaustive
literature review and must not be read as a universal absence result.

## Frozen comparison axes

### P1 — Independently specified, non-definitionally-induced target semantics

`SatPsi` is specified independently rather than being definitionally obtained
from `SatPhi` and the reporting map. This does not mean arbitrary unrelated
semantics: current M3 separately imposes a bridge obligation through
`ResidualFaithfulness`. The relevant distinction is not merely “two
semantics.”

### P2 — Post-hoc projection

A low-level solution or repair family is obtained first and then mapped
many-to-one into another representation or reporting space. This mechanism is
not an M3 novelty claim.

### P3 — Projection/minimization interaction

The work substantially studies projection followed by minimization,
re-minimization, or equality or containment relationships between low-level
minimal solutions and their projected minimal family. Projection-then-minimize
is not an M3 novelty claim.

### P4 — Cross-semantic frontier decomposition

The target question is whether exact equality between a low-level/report-derived
minimal frontier and an independently specified target-semantic minimal
frontier can be decomposed into explicit cross-semantic proof obligations.

The proposed factorization `GC <-> FS ∧ CRLift` is **not currently a theorem in
the repository**. `FrontierSoundness`, `CRLift`, and `ReverseLiftability` are
not current Lean declarations. This factorization is only a proposed
theoretical sharpening. The current theorem is recorded in
[Current kernel-checked M3 boundary](#current-kernel-checked-m3-boundary).

### P5 — Pre-group / post-hoc equivalence

The target question is when coarse or pre-grouped repair search is
extensionally equivalent to fine-grained repair followed by post-hoc
reporting. M3-A already supplies an atomic sufficient regime. The future
novelty candidate is not merely that pre-grouping can work; it is to
characterize conditions weaker than atomicity under which pre-grouped search
and fine-grained repair followed by reporting coincide.

### P6 — Target-side closure boundary

Use “target-side closure boundary,” not “implementation-side deletion
monotonicity.” The current M3 property is
`PsiDeletionMonotonicity I SatPsi`:

```text
T' ⊆ T ⊆ I and SatPsi T imply SatPsi T'.
```

Thus, deleting more contract atoms cannot destroy target/reference
satisfiability.

- M3-B sufficiency does not require this monotonicity.
- `m3c_converse` requires target-side `PsiDeletionMonotonicity`.
- `audit_cost_collapse` uses target-side `PsiDeletionMonotonicity`.
- `audit_cost_collapse` does not assume deletion monotonicity of `SatPhi`.

The research question is: Which target-side closure condition turns grouped
exactness into full report soundness and permits audit reduction to raw minimal
repairs?

### P7 — Graded assurance under incomplete evidence

The future question is how guarantees degrade from emitted-report soundness,
to soundness over a covered region, to global exactness when the repair
frontier is incomplete. This is not currently formalized in the Lean core.
Diagnosis and approximation literature may provide close prior ideas; generic
treatment of incomplete enumeration is not claimed as novel.

### P8 — Reporting-aware certificate contract

This axis distinguishes certificates or checkers in general from a semantic
contract specifying which evidence must be certified to justify reporting
exactness. Candidate B currently supplies artifact evidence and checker
architecture. It does not prove a general theorem of the form
`certificate evidence -> exact reportability`. Such a theorem is only a
proposed system and assurance contribution.

## Frozen 7 × 8 literature matrix

| Prior work | P1 Non-definitionally-induced target semantics | P2 post-hoc projection | P3 projection/minimization | P4 cross-semantic frontier decomposition | P5 pre-group / post-hoc equivalence | P6 target-side closure boundary | P7 graded assurance under incomplete evidence | P8 reporting-aware certificate contract |
|---|---|---|---|---|---|---|---|---|
| Mozetić 1991 | No△ | No | No | No△ | No | No | No△ | No |
| Chittaro & Ranon 2004 | No△ | No | No | No△ | No△ | No | No | No |
| Autio & Reiter 1998 | not reported† | not reported† | not reported† | not reported† | unknown† | unknown† | unknown† | unknown† |
| Grastien et al. 2023 | No | Yes | Yes | No△ | No | No / not the M3 condition | No | No |
| MSMP 2013 | No | No | No | No | No | No△ | No | No△ |
| Leo & Tack / FindMUS | No | No | No | No | No△ | No△ | No△ | No |
| Abstract-interpretation completeness | No△ | No | No△ | No△ | No | No△ | No△ | No△ |

The classifications mean:

- `Yes`: substantially treats the axis.
- `No`: not found in the reviewed material.
- `No△`: does not instantiate this axis, but contains a strong adjacent
  theorem, mechanism, or counterexample.
- `not reported†`: the original source was unavailable; a reliable secondary
  characterization supports the stated absence for that axis.
- `unknown†`: the original source was unavailable and the secondary evidence
  is insufficient for an absence claim.

Neither `not reported†` nor `unknown†` may be converted into unconditional
`No`. The matrix is not an exhaustive proof that no prior work anywhere
contains a concept or an equivalent idea under different terminology.

## Current kernel-checked M3 boundary

### Independent predicates

The core takes separate, explicit predicate arguments:

```text
SatPhi : Finset Lever -> Prop
SatPsi : Finset Atom -> Prop
```

`SatPsi` is therefore non-definitionally-induced: it is not defined from
`SatPhi` or from `groupTouchAny`. Separate specification does not remove the
bridge obligations below.

### ResidualFaithfulness

`ResidualFaithfulness I beta SatPsi SatPhi` is block-aligned residual
agreement. Its definition requires, for every active `T`:

```text
T ⊆ I -> (SatPhi (betaSet beta T) <-> SatPsi T)
```

It is an equivalence on block-aligned retained sets, not merely one-directional
soundness.

### M3-B sufficiency

The theorem `m3b_grouped_correctness` proves the following chain without
atomicity and without any deletion-monotonicity assumption:

```text
BlocksDisjoint
+ ResidualFaithfulness
+ GroupSoundness
=>
forall G,
  GroupedRepair G <-> ContractRepair G
```

Here and below, displayed repair predicates suppress the unchanged parameters
`I`, `beta`, `SatPhi`, and `SatPsi` for readability.

### M3-C exactness

Under

```text
BlocksDisjoint
+ ResidualFaithfulness
+ PsiDeletionMonotonicity
```

the theorem `groupSoundness_iff` proves:

```text
GroupSoundness
<->
forall G,
  GroupedRepair G <-> ContractRepair G
```

This is the current exact characterization. It must not be rewritten as the
proposed `GC <-> FS ∧ CRLift` factorization.

### Converse

`m3c_converse` uses target-side `PsiDeletionMonotonicity` and pointwise grouped
correctness to derive `GroupSoundness`. `ResidualFaithfulness` is absent from
the converse itself.

### Audit-cost collapse

`audit_cost_collapse` proves that, under target-side
`PsiDeletionMonotonicity`, checking target feasibility only for raw minimal
repairs suffices to establish unrestricted `GroupSoundness`. The finite descent
does not assume deletion monotonicity of `SatPhi`.

### Atomic regime

`rawRepair_betaSet_iff_contractRepair` gives exact block-aligned raw/contract
minimal-repair correspondence under the M3-A atomic regime. The hierarchy
theorem `atomicity_implies_groupSoundness` shows that atomicity, together with
the theorem's disjointness and residual-faithfulness hypotheses, implies
`GroupSoundness`.

## Current and proposed contributions

| Status | Contribution |
|---|---|
| `ESTABLISHED_SUBSTRATE_NOT_NOVELTY` | projection/re-minimization, minimal-set machinery, and grouping as such |
| `CURRENT_THEOREM` | independently specified non-definitionally-induced `SatPsi`; M3-B sufficiency; M3-C exactness under target-side monotonicity |
| `CURRENT_ARTIFACT_EVIDENCE` | Candidate B independent finite audit/checker workflow |
| `PROPOSED_THEOREM` | `GC <-> FS ∧ CRLift` frontier factorization |
| `PROPOSED_THEOREM` | weaker-than-atomic pre-group/post-hoc equivalence boundary |
| `PROPOSED_THEOREM` | incomplete-evidence assurance hierarchy |
| `PROPOSED_SYSTEM_CONTRIBUTION` | reporting-aware certificate/checker contract |

The status of every proposed item is explicit:

- `GC <-> FS ∧ CRLift` frontier factorization — **NOT CURRENTLY PROVED IN THE REPOSITORY**.
- Weaker-than-atomic pre-group/post-hoc equivalence boundary — **NOT CURRENTLY PROVED IN THE REPOSITORY**.
- Incomplete-evidence assurance hierarchy — **NOT CURRENTLY PROVED IN THE REPOSITORY**.
- Reporting-aware certificate/checker contract — **NOT CURRENTLY PROVED IN THE REPOSITORY**.

No placeholder Lean declarations are introduced for these proposals.

## Paper-facing interpretation

The current paper-facing research question is:

> When may verified low-level repairs be reinterpreted under an independently
> specified reporting semantics?

The current Lean theorem answers this question through the existing M3
vocabulary:

- `ResidualFaithfulness`;
- `GroupSoundness`;
- `PsiDeletionMonotonicity`;
- `GroupedRepair`; and
- `ContractRepair`.

It does not answer the question through `GC <-> FS ∧ CRLift`. The proposed
future questions are separate:

1. Can grouped frontier exactness be factored into independently auditable
   forward/reverse obligations?
2. What conditions weaker than atomicity make pre-grouped repair search
   extensionally equivalent to fine-grained repair followed by reporting?
3. What reportability guarantees survive incomplete frontier evidence?
4. Can these guarantees be exposed as a reporting-aware certificate contract?

## Prior-art discipline

### Grastien et al. 2023

Grastien et al. 2023 is strong neighboring prior art for P2 and P3. M3 does
not claim novelty for post-hoc projection, projection followed by
re-minimization, or the fact that abstraction can change a minimal family.
Nor does this note claim that Grastien et al. lack all forms of soundness or
completeness theory.

The narrower distinction recorded here is that M3 permits `SatPsi` to be
specified separately rather than definitionally induced by projection from
the low-level diagnosis or repair semantics, and makes correctness of the
resulting report an explicit cross-semantic obligation.

### Autio & Reiter 1998

The unavailable original is not reconstructed or inferred. `not reported†`
is used only where reviewed secondary literature supports the stated
classification; `unknown†` is used where it does not support an absence claim.
Manuscript prose must not turn either classification into a universal absence
claim without inspection of the original source.

## Required non-claims

This audit does not establish:

- exhaustive coverage of all repair literature;
- universal novelty of independent reporting semantics;
- that `GC <-> FS ∧ CRLift` is currently proved;
- that P5's weaker-than-atomic boundary is currently known;
- that incomplete-evidence assurance is currently formalized;
- that Candidate B proves a generic certificate theorem;
- that Dafny Case B establishes M3 `GroupSoundness` or M3 exactness; or
- that all prior work marked `No` could not contain an equivalent idea under
  different terminology.

## Consistency-search findings

The repository was searched for `implementation monotonicity`, `SatPhi
monotonicity`, `deletion monotonicity`, `FrontierSoundness`, `CRLift`,
`ReverseLiftability`, `GC`, `pre-group`, `reportability`, and
`groupSoundness_iff`. Findings are classified as follows.

| Classification | Location and finding |
|---|---|
| `CURRENT_AND_CORRECT` | `SocialChoiceAtlas/Reportability/Defs.lean` defines target-side `PsiDeletionMonotonicity`; `SocialChoiceAtlas/Reportability/Monotone.lean` uses it in `audit_cost_collapse`, `m3c_converse`, and `groupSoundness_iff`, while explicitly excluding `SatPhi` deletion monotonicity. |
| `CURRENT_AND_CORRECT` | `papers/cpp2027_m1_5_m3/main.tex` states deletion monotonicity on the reference predicate and accurately presents the current sufficiency, converse, and characterization. It does not present the proposed factorization as current. |
| `CURRENT_AND_CORRECT` | `docs/research_program_current.md`, `RESEARCH_STATUS.md`, `README.md`, `tools/cpp2027/README_REPRODUCE.md`, and Candidate B claim/reproduction files describe the existing M3 declarations or finite artifact audit without introducing the proposed declarations. |
| `STALE_BUT_HISTORICAL` | `docs/m3_canonical_integration_precheck.md` uses the old audit-row label “Implementation monotonicity,” but the row's substance says correctly that no theorem assumes deletion monotonicity of `SatPhi`. The document is a historical integration precheck and was not rewritten. |
| `STALE_BUT_HISTORICAL` | `docs/doctoral_scope_lock.md` contains a historical progress snapshot saying the M3 theorem core was off-main with integration pending. The document's own authority rules defer current milestone status to `docs/research_program_current.md`; it was not rewritten. |
| `STALE_AND_PAPER_RELEVANT` | None found. The current paper uses the implemented vocabulary and theorem boundary. |
| `PROPOSED_NOT_IMPLEMENTED` | No pre-existing repository declaration or theorem named `FrontierSoundness`, `CRLift`, or `ReverseLiftability` was found, and no pre-existing `GC <-> FS ∧ CRLift` claim was found. The P4, P5, P7, and P8 proposals are recorded only as future work in this freeze. |

No searched location incorrectly presents a proposed concept as a current
theorem.

## Freeze validation

```text
MATRIX_ROWS = 7
MATRIX_AXES = 8
LEAN_DECLARATION_MISMATCH = 0
SATPHI_MONOTONICITY_MISCLAIM = 0
CURRENT_FUTURE_CONFLATION = 0
AUTIO_REITER_OVERCLAIM = 0
GRASTIEN_OVERCLAIM = 0
MANUSCRIPT_EDITED = 0
LEAN_EDITED = 0
NEW_EXPERIMENTS = 0
M3_PRIOR_ART_CLAIM_MATRIX_FREEZE = PASS
```
