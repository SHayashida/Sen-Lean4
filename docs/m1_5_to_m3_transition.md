# M1.5 to M3 Transition

## 1. One-Line Spine

M1.5 shows that raw repair explanations need not be canonical even under
clause-multiset equivalence. M3 shows that report-level repair canonicity is a
contract-relative property: it is guaranteed by suitable interface and
soundness conditions, and Candidate B demonstrates this distinction on the same
witness.

The dissertation-level structure is:

```text
M1.5 -> M3-A / M3-B / M3-C
     -> Candidate B artifact-backed instantiation.
```

## 2. What M1.5 Established

M1.5 is a negative result about raw repair reportability. It shows that
`equiv_CM`, or clause-multiset equivalence, is insufficient to make raw
lever-level repair explanations canonical.

Candidate B supplies the relevant witness:

- the bundled side represents `minlib` as one repair atom;
- the split side refines it into `decisive_voter0` and
  `decisive_voter1`;
- the raw minimal repairs differ across the bundled and split
  implementations.

Therefore, a valid impossibility certificate or clause-equivalent encoding
does not automatically determine a canonical raw repair presentation.

M1.5 exposes a reportability gap: proof/certificate equivalence does not by
itself fix the level at which repairs may be reported.

This transition takes the M1.5 result as established. It does not reprove RENI
and makes no claim beyond the declared Candidate B artifact scope.

## 3. Failure Mechanism Extracted from M1.5

Raw repair operates over implementation levers. Reported repair operates over
contract atoms. These are different domains.

When one contract atom is refined into multiple independently removable
implementation levers, deleting only part of the block can become a raw
minimal repair. Such a deletion is not directly expressible at the original
bundled atom level unless a reportability contract specifies how
implementation deletions are grouped.

partial-block deletion escapes the block-aligned contract interface unless a reporting contract closes the gap.

This mechanism explains why raw repair non-canonicity can coexist with
propositional equivalence or exact clause-multiset equivalence. Equivalence of
the encoded constraints does not itself identify the reporting domain or the
map from implementation repairs to that domain.

## 4. What M3 Adds

M3 develops a positive, contract-relative theory. It assumes an explicit
reportability contract rather than treating the implementation lever set as
the reporting vocabulary by default.

M3 separates two axes:

- the **truth/certificate axis**, which asks whether implementation residuals
  correctly represent and certify the reference residual problems;
- the **repair/report axis**, which asks when implementation-level deletions
  may be reported as contract-level repairs.

Residual faithfulness connects block-aligned implementation residuals to the
contract reference residuals. Grouped reporting is not automatic; it must be
justified by theorem conditions. `GroupedInvariance` is a theorem-level
property, not part of the definition of the contract, realization, raw repair
family, or grouping map.

M3 does not say that raw repairs become canonical. It says that, under explicit
contract conditions, grouped repair reports can be canonical even when raw
repairs are not.

## 5. M3-A: Atomicity as the Syntactic Sufficient Condition

M3-A states:

```text
RepairAtomicity + ResidualFaithfulness => GroupedInvariance.
```

Atomicity gives each active contract atom exactly one active implementation
lever. Consequently, every implementation-level deletion is block-aligned,
and block-aligned residual faithfulness covers all feasibility and minimality
queries made by the raw repair definition.

M3-A also gives exact raw repair transport under the atom-induced bijection
between two atomic realizations. It is syntactic and immediately auditable:
check whether every active `beta(a)` has cardinality one.

This theorem does not apply to the M1.5 split realization under the bundled
`minlib` contract, because:

```text
beta(minlib) = {decisive_voter0, decisive_voter1}
```

is non-atomic. M3-A alone must therefore not be described as establishing
contract-level canonicity for Candidate B.

## 6. M3-B: Group-Soundness as the Non-Atomic Sufficient Condition

M3-B allows non-atomic implementations. It requires:

```text
GroupSoundness(E, C).
```

This condition says that every feasible arbitrary implementation deletion,
once grouped to contract atoms, must be feasible in the reference contract.
Together with residual faithfulness, it gives:

```text
GroupedRep_C(E) = ContractRep(C).
```

For two realizations of the same contract, applying M3-B separately yields
grouped invariance through the shared `ContractRep(C)`. M3-B gives grouped
invariance only; it does not give exact raw repair transport.

M3-B directly answers the objection that atomicity merely forbids the M1.5
pathology:

> M3-A prevents partial-block escape syntactically.  
> M3-B permits partial-block deletion, but requires it to remain sound after
> grouping.

## 7. M3-C: Exactness Under Deletion-Monotone Contracts

M3-C is a candidate converse and theorem skeleton. Its scope is defined by:

```text
PsiDeletionMonotonicity(C).
```

This says that deleting more contract atoms cannot destroy satisfiability. It
is natural for standard conjunctive axiom-deletion contracts, where deleting
atoms removes constraints. It is not assumed for arbitrary reportability
contracts.

Under `PsiDeletionMonotonicity`, grouped correctness implies
`GroupSoundness`. This reverse direction does not require residual
faithfulness.

The two directions are asymmetric:

```text
Forward direction:
  GroupSoundness + ResidualFaithfulness
  => Grouped correctness.

Reverse direction:
  Grouped correctness + PsiDeletionMonotonicity
  => GroupSoundness.
```

Combining M3-B and candidate M3-C, for residually faithful realizations over
`Psi`-deletion-monotone contracts, `GroupSoundness` characterizes grouped
report correctness.

The monotonicity assumption is not removable: a non-monotone counterexample
in the M3-B/C skeleton exhibits grouped correctness without GroupSoundness.

## 8. Candidate B Instantiation

Candidate B has now been audited as an artifact-defined instantiation of M3-B.

The bundled-level artifact-defined contract is:

```text
I = {asymm, un, minlib, no_cycle4}.
```

`no_cycle3` is inactive in this contract scope. The split realization uses:

```text
beta(minlib) = {decisive_voter0, decisive_voter1}.
```

The artifact-only audit verified:

1. the fully active bundled and split residuals are UNSAT;
2. implementation-deletion-closure over the declared split interface;
3. all 16 block-aligned residual comparisons match;
4. split `RawRep` is exactly the five singleton repairs;
5. the grouped reports map to bundled SAT residuals;
6. `PsiDeletionMonotonicity` holds over the complete 16-row bundled lattice;
7. no solver was run.

Although `GroupSoundness` quantifies over arbitrary implementation deletions,
under a deletion-monotone contract the audit-cost collapse lemma reduces its
audit to the complete `RawRep` family. This is why the Candidate B
instantiation could be checked by artifact reanalysis without a new solver
run.

The result is:

> Candidate B instantiates M3-B under the bundled-level artifact-defined
> contract.

The grouped repair family is:

```text
{
  {asymm},
  {un},
  {minlib},
  {no_cycle4}
}
```

The two levels must be stated separately.

**Raw level:** Candidate B remains non-canonical across bundled and split
implementations.

**Grouped contract level:** Under the bundled-level artifact-defined contract,
verified residual faithfulness, verified `GroupSoundness`, and touch-any
grouping, the grouped repair report is canonical.

## 9. Correct Use of “Recovery”

The term “recovery” is legitimate only in the contract-level sense established
by the Candidate B audit.

Allowed wording:

> M3-B recovers report-level canonicity on the same witness, after the
> reportability contract is made explicit and GroupSoundness is verified.

Forbidden wording:

> M3 erases the M1.5 non-canonicity.  
> M3 makes the raw repairs canonical.  
> M3 shows that the bundled and split raw repairs are the same.

The precise formulation is:

> Candidate B is raw-noncanonical and contract-canonical at the same time.

M1.5 is not weakened or invalidated. M3 refines M1.5 by separating raw
implementation-level repairs from contract-level reported repairs. The same
witness now plays both roles:

- negative at the raw level;
- positive at the grouped contract level.

## 10. Artifact-Defined Contract Scope

The Candidate B instantiation uses an artifact-defined bundled contract `C_b`,
where `Psi_b(T)` is represented by the bundled residual recorded in the
Candidate B artifacts.

This is enough for the M3-B audit result inside the declared artifact scope.
It must not be silently identified with a fully semantic or Lean-level
reference contract.

The distinction is:

- **Artifact-defined contract:** reference residuals are the bundled residuals
  recorded in artifacts.
- **Semantic contract:** reference residuals are independently justified as
  the intended social-choice problems.
- **Lean/formal contract:** reference residuals are tied to formal definitions
  and theorems.

Upgrading the artifact-defined contract to a semantic or Lean-level contract
is a separate faithfulness obligation. It belongs to the broader M1/M2
truth/certificate axis and must not be assumed in this transition document.

## 11. Dissertation-Level Role

The progression is now explicit:

- M1.5 established the reportability gap.
- M3-A gives a simple syntactic sufficient condition.
- M3-B gives a group-soundness-based non-atomic sufficient condition.
- M3-C gives a candidate exactness result under deletion-monotone reference
  contracts.
- Candidate B demonstrates the theory on the same witness that exposed the
  gap.

Auditable social-choice evidence therefore requires:

1. correct certificates;
2. explicit reportability contracts;
3. conditions showing when implementation-level repairs may be reported as
   contract-level repairs.

M1.5 shows why reportability cannot be assumed; M3 shows how reportability can be earned.

## 12. What This Document Does Not Do

- It does not reprove RENI.
- It does not formalize M3-A, M3-B, or M3-C in Lean.
- It does not extend Candidate B beyond the declared artifact-defined scope.
- It does not claim full semantic validity of the bundled contract.
- It does not address Arrow transfer.
- It does not introduce M4 governance delegation.
- It does not add a six-layer taxonomy.

The next prerequisite testbed is the Arrow transfer question, recorded
separately in the M3 completion criteria.

## 13. Acceptance Criteria

- Exactly one file is created:
  `docs/m1_5_to_m3_transition.md`.
- No code is changed.
- No solver is run.
- No new experiment is performed.
- The document uses the structure:
  `M1.5 -> M3-A / M3-B / M3-C -> Candidate B artifact-backed instantiation`.
- “Recovery” appears only in the explicitly qualified contract-level section.
- Raw non-canonicity remains distinct from grouped contract-level canonicity.
- The artifact-defined contract remains distinct from semantic and Lean-level
  contracts.
- No application implementation or six-layer taxonomy is introduced.
