# M3 Non-Atomic Group-Soundness Skeleton

## 1. Motivation

Atomicity is a strong sufficient condition. Since M1.5 non-canonicity arises
when one contract atom is refined into multiple independently removable
levers, a reviewer may object that atomicity merely forbids the pathology.

M3-A remains useful as a mechanically checkable sufficient condition, but M3
should test whether a weaker non-atomic sufficient condition exists.

The purpose of M3-B is to allow non-atomic refinements while requiring that
partial implementation-level repairs remain sound as contract-level reports.

## 2. Core Idea

Non-atomic implementations should be allowed when every arbitrary
implementation-level deletion that restores satisfiability has a sound grouped
interpretation at the contract level.

> partial-block deletion is allowed, but it must not escape the contract report.

A partial deletion inside a non-atomic block may be a valid raw implementation
repair, but once grouped to contract atoms, the reported repair must also be
feasible in the reference contract.

## 3. Definitions

This note reuses the definitions from
[`docs/m3_reportability_contract.md`](m3_reportability_contract.md) and
[`docs/m3_atomicity_theorem_skeleton.md`](m3_atomicity_theorem_skeleton.md).
Only the objects needed for M3-B are restated.

Let:

```text
C = (A, I, Psi, label, report_policy)
```

where `I subseteq A` and `Psi(T)` is defined for every `T subseteq I`.

Let:

```text
E = (B, Lambda, beta, phi_E, evidence)
```

with active implementation interface:

```text
Lambda_I = union_{a in I} beta(a).
```

Use touch-any grouping:

```text
group_E(R) = {a in I | R intersects beta(a)}.
```

Define:

```text
GroupSoundness(E, C) :iff
  for every R subseteq Lambda_I,
    SAT(phi_E(B, Lambda_I \ R))
    implies
    SAT(Psi(I \ group_E(R))).
```

If an arbitrary implementation-level deletion is feasible, then deleting the
grouped contract atoms it touches is feasible in the reference contract.

Keep residual faithfulness unchanged:

```text
ResidualFaithfulness(E, C) :iff
  for every T subseteq I,
    SAT(phi_E(B, beta(T))) iff SAT(Psi(T)).
```

`GroupSoundness` is not a comparison between two realizations. It is a
single-realization soundness condition relating arbitrary implementation
deletions to the fixed contract report.

## 4. Candidate Theorem M3-B

### Theorem M3-B: Non-atomic grouped report correctness under group-soundness

The intended repair setting is the fully active UNSAT case. If the fully
active reference and implementation residuals are already SAT, the repair
families degenerate to the empty deletion case; this note focuses on the
UNSAT repair setting.

If `E` is implementation-deletion-closed, residually faithful, and group-sound
relative to `C`, then:

```text
GroupedRep_C(E) = ContractRep(C).
```

No atomicity assumption is required.

### Two-realization corollary

If `E1` and `E2` are both implementation-deletion-closed, residually faithful,
and group-sound relative to `C`, then:

```text
GroupedRep_C(E1) = ContractRep(C) = GroupedRep_C(E2).
```

This theorem does not claim raw repair transport. It gives grouped report
invariance only.

## 5. Proof Skeleton

### Lemma B1: Contract repairs appear in the grouped raw image

**Statement.** For every `G in ContractRep(C)`, there exists
`R in RawRep(E)` such that:

```text
group_E(R) = G.
```

**Proof idea.** Since `G in ContractRep(C)`:

```text
SAT(Psi(I \ G)).
```

By residual faithfulness:

```text
SAT(phi_E(B, beta(I \ G))).
```

The active blocks are pairwise disjoint and
`Lambda_I = beta(I)`, so:

```text
beta(I \ G) = Lambda_I \ beta(G).
```

Thus deleting `beta(G)` is feasible on the implementation side. Consider the
finite nonempty family:

```text
{R subseteq beta(G) | SAT(phi_E(B, Lambda_I \ R))}.
```

It is nonempty because `beta(G)` itself is feasible. Choose an
inclusion-minimal feasible `R` in this family.

Then `R in RawRep(E)`: every `R' proper-subset R` is automatically a subset of
`beta(G)`, so minimality inside `beta(G)` is enough for global raw minimality
with respect to proper subsets of `R`.

Since `R subseteq beta(G)`, touch-any grouping gives:

```text
group_E(R) subseteq G.
```

By `GroupSoundness`:

```text
SAT(Psi(I \ group_E(R))).
```

Since `G` is contract-minimal and `group_E(R) subseteq G`, it follows that:

```text
group_E(R) = G.
```

The proof does not assume deletion-monotonicity of `phi_E`; only finiteness and
the existence of inclusion-minimal feasible deletions are used.

### Lemma B2: Grouped raw reports are contract-feasible

**Statement.** For every `R in RawRep(E)`:

```text
SAT(Psi(I \ group_E(R))).
```

**Proof idea.** This is immediate from `GroupSoundness`, because
`R in RawRep(E)` implies:

```text
SAT(phi_E(B, Lambda_I \ R)).
```

Therefore every grouped raw report is a feasible contract-level deletion,
although it need not itself be contract-minimal.

### Lemma B3: Every grouped raw report contains a contract-minimal repair

**Statement.** For every `R in RawRep(E)`, there exists
`G0 in ContractRep(C)` such that:

```text
G0 subseteq group_E(R).
```

**Proof idea.** By Lemma B2, `group_E(R)` is contract-feasible. Since the
contract domain `I` is finite, the family:

```text
{
  G subseteq group_E(R)
  | SAT(Psi(I \ G))
}
```

is finite and nonempty. Choose an inclusion-minimal member `G0`. Every proper
subset of `G0` is also contained in `group_E(R)` and is infeasible by the
choice of `G0`. Therefore `G0 in ContractRep(C)`.

Again, no deletion-monotonicity assumption is required.

### Lemma B4: Minimized grouped image equals ContractRep

**Statement.**

```text
Min_subseteq {group_E(R) | R in RawRep(E)} = ContractRep(C).
```

**Proof idea.** First, Lemma B1 gives:

```text
ContractRep(C)
  subseteq {group_E(R) | R in RawRep(E)}.
```

Second, let `M` be a minimal element of the grouped raw image. Then
`M = group_E(R)` for some `R in RawRep(E)`. By Lemma B3, there exists
`G0 in ContractRep(C)` with:

```text
G0 subseteq M.
```

By Lemma B1, `G0` itself is also in the grouped raw image. Since `M` is minimal
in that image:

```text
M = G0.
```

Therefore every minimal grouped raw report is in `ContractRep(C)`.

Conversely, let `G in ContractRep(C)`. Lemma B1 places `G` in the grouped raw
image. If a proper subset `M` of `G` were also in that image, Lemma B3 would
give `G0 in ContractRep(C)` with `G0 subseteq M proper-subset G`. This would
contradict the inclusion-minimality of `G`. Hence every member of
`ContractRep(C)` survives `Min_subseteq`.

Thus:

```text
GroupedRep_C(E) = ContractRep(C).
```

### Theorem M3-B

Apply Lemma B4.

### Corollary: Two-realization grouped invariance

Apply M3-B separately to `E1` and `E2` and compose both equalities through
`ContractRep(C)`.

## 6. Relation to M3-A

- M3-A uses atomicity to ensure every raw deletion is block-aligned.
- M3-B allows non-atomic blocks, but requires arbitrary partial deletions to be
  group-sound.
- M3-A is syntactic and immediately checkable: the auditor checks whether each
  active `beta(a)` has cardinality one.
- M3-B is semantic and requires either proof or finite exhaustive checking of
  `GroupSoundness`.
- This audit-cost asymmetry is why both theorem forms are useful.
- Atomicity plus residual faithfulness implies `GroupSoundness`.
- M3-A additionally gives exact raw repair transport under the atom-induced
  lever bijection.
- M3-B gives grouped invariance only, not raw transport.

`GroupSoundness` can be weakened to minimal raw repairs only, because the proof
applies it only to members of `RawRep(E)` and to the minimal feasible deletions
chosen in Lemma B1. However, the theorem should keep the unrestricted
`for every R subseteq Lambda_I` version. The unrestricted version is
independent of computing `RawRep(E)` and is cleaner as an audit condition.

## 6.5 Candidate converse under contract deletion-monotonicity

Define contract deletion-monotonicity by:

```text
PsiDeletionMonotonicity(C) :iff
  for all T' subseteq T subseteq I,
    SAT(Psi(T)) implies SAT(Psi(T')).
```

Here `T` is the retained active-atom set. Smaller `T` means more contract atoms
have been deleted. Thus, `PsiDeletionMonotonicity` says deleting more contract
atoms cannot destroy satisfiability.

This condition is natural for standard conjunctive axiom-deletion contracts,
where each atom contributes constraints and deleting atoms removes constraints.
It is not assumed for arbitrary reportability contracts unless stated.

### Candidate Theorem M3-C: Grouped correctness implies group-soundness

**To be verified.** If `PsiDeletionMonotonicity(C)` holds, then:

```text
GroupedRep_C(E) = ContractRep(C)
implies
GroupSoundness(E, C).
```

This direction does not require residual faithfulness.

**Proof sketch.** Let `R subseteq Lambda_I` be feasible:

```text
SAT(phi_E(B, Lambda_I \ R)).
```

Choose an inclusion-minimal feasible `R0 subseteq R`. Then
`R0 in RawRep(E)`, because every strict subset of `R0` is also a subset of `R`
and is infeasible by the choice of `R0`. Since `R0 subseteq R`, touch-any
grouping is monotone:

```text
group_E(R0) subseteq group_E(R).
```

Choose a minimal grouped-image element `M` with:

```text
M subseteq group_E(R0).
```

Then `M in GroupedRep_C(E)`. By the assumed equality:

```text
M in ContractRep(C).
```

Therefore:

```text
SAT(Psi(I \ M)).
```

Since `M subseteq group_E(R)`:

```text
I \ group_E(R) subseteq I \ M.
```

By `PsiDeletionMonotonicity(C)`:

```text
SAT(Psi(I \ group_E(R))).
```

This proves `GroupSoundness(E, C)`.

The converse uses monotonicity of `Psi`, not deletion-monotonicity of `phi_E`.

### Equivalence Corollary

For residually faithful realizations over `Psi`-deletion-monotone contracts:

```text
GroupSoundness(E, C)
iff
GroupedRep_C(E) = ContractRep(C).
```

The forward direction is M3-B and uses residual faithfulness but not
monotonicity. The reverse direction is candidate M3-C and uses
`PsiDeletionMonotonicity(C)` but not residual faithfulness.

`GroupSoundness` is not a definition of grouped invariance. It is a
per-deletion soundness condition over arbitrary implementation residuals.
M3-C says that, for deletion-monotone reference contracts, this condition is
exact: any realization whose grouped reports are correct must already be
group-sound.

A one-atom, two-lever realization with:

```text
I = {a}
Lambda_I = {x, y}
beta(a) = {x, y}
RawRep(E) = {{x}, {y}}
group_E({x}) = group_E({y}) = {a}
GroupedRep_C(E) = {{a}}
ContractRep(C) = {{a}}
```

shows that non-atomic but group-sound realizations can exist. This demonstrates
that M3-B is not equivalent to M3-A.

### Why contract deletion-monotonicity is substantive

The monotonicity assumption is not cosmetic. Without it, grouped correctness
need not imply unrestricted `GroupSoundness`.

Consider the following schematic counterexample:

```text
I = {a, b}

Psi({a, b}) = UNSAT
Psi({b})    = SAT
Psi({a})    = UNSAT
Psi(empty)  = UNSAT

beta(a) = {x1, x2}
beta(b) = {y}

RawRep(E) = {{x1}}
group_E({x1}) = {a}
GroupedRep_C(E) = {{a}} = ContractRep(C)
```

Suppose a larger feasible deletion `R = {x1, y}` also exists. Then:

```text
group_E(R) = {a, b}.
```

But:

```text
Psi(I \ {a, b}) = Psi(empty) = UNSAT,
```

so `GroupSoundness` fails even though grouped correctness holds. This shows
that `PsiDeletionMonotonicity` is the bridge that extends soundness from
minimal grouped reports to arbitrary feasible implementation deletions. This
is a schematic counterexample, not an experiment.

### Audit-cost collapse under Psi-deletion-monotonicity

If `PsiDeletionMonotonicity(C)` holds, then it is enough to check
`GroupSoundness` on raw minimal repairs:

```text
for every R in RawRep(E),
  SAT(Psi(I \ group_E(R))).
```

This condition implies unrestricted `GroupSoundness`.

**Proof idea.** Any feasible implementation deletion contains an
inclusion-minimal feasible subdeletion `R0 in RawRep(E)`. Since
`R0 subseteq R`, touch-any grouping gives:

```text
group_E(R0) subseteq group_E(R).
```

Raw-repair soundness gives:

```text
SAT(Psi(I \ group_E(R0))).
```

The retained set `I \ group_E(R)` is a subset of
`I \ group_E(R0)`, so `PsiDeletionMonotonicity(C)` gives:

```text
SAT(Psi(I \ group_E(R))).
```

This is why a Candidate B audit may reduce to checking the grouped reports of
the split-side raw repairs rather than all `2^|Lambda_I|` deletion subsets.

### Implementation monotonicity note

The converse uses monotonicity of `Psi`, not deletion-monotonicity of `phi_E`.
However, in clause-family deletion encodings, if implementation deletion
monotonicity and residual faithfulness both hold on block-aligned residuals,
then `PsiDeletionMonotonicity` can often be inherited on the reference side.
This inheritance should be recorded as a separate audit fact, not assumed
silently.

## 7. Relation to M1.5

- M1.5 shows raw repair non-canonicity under `≡CM`.
- M1.5 does not by itself rule out contract-level grouped invariance.
- Under a bundled-level contract where `minlib` is one contract atom and the
  split realization has
  `beta(minlib) = {decisive_voter0, decisive_voter1}`, the raw split repairs
  `{decisive_voter0}` and `{decisive_voter1}` both group to `{minlib}` under
  touch-any reporting.
- Therefore the M1.5 witness may exhibit raw non-canonicity and contract-level
  grouped canonicity simultaneously, if `GroupSoundness` holds for the declared
  contract and realization.
- M3-B must not claim this as established until the relevant `GroupSoundness`
  check is verified from artifacts or by proof.

M1.5 exposes raw-level non-canonicity. M3-B tests whether the same non-atomic
witness can be made reportable at the contract level.

M3-B does not automatically recover the M1.5 witness. That conclusion remains
conditional on verifying `GroupSoundness` for the declared contract and
realization.

## 8. Candidate B Artifact Implication

The Candidate B witness from M1.5 becomes a natural first audit target for
M3-B.

The intended check is:

- contract atoms at the bundled level:
  `asymm`, `un`, `minlib`, `no_cycle4`;
- split realization:
  `beta(minlib) = {decisive_voter0, decisive_voter1}`;
- touch-any grouping: `{decisive_voter0}` and `{decisive_voter1}` both report
  as `{minlib}`;
- expected grouped family:
  `{asymm}`, `{un}`, `{minlib}`, `{no_cycle4}`.

The next document, not this one, should inspect existing Candidate B artifacts
to determine whether `GroupSoundness` holds for all required
`R subseteq Lambda_I`. This note does not perform that check.

## 9. Go / No-Go Criteria

### Go if

- the proof skeleton closes without assuming grouped invariance;
- `GroupSoundness` is independent of equality between realizations;
- `GroupSoundness` is strictly weaker than atomicity in the sense that
  non-atomic realizations can satisfy it;
- M3-A remains useful as the syntactic, easily auditable condition;
- M3-B explains how non-atomic implementations may still support invariant
  grouped reports;
- the theorem does not require deletion-monotonicity of `phi_E`.

The strictness requirement is witnessed abstractly by the one-atom,
two-lever realization in Section 6.5. `GroupSoundness` constrains residual SAT
implications, not block cardinalities.

### No-Go if

- `GroupSoundness` collapses into the theorem conclusion;
- the proof requires assuming `GroupedRep_C(E) = ContractRep(C)`;
- the condition is equivalent to atomicity;
- the theorem cannot handle arbitrary `R subseteq Lambda_I`;
- the proof secretly requires deletion-monotonicity.

### Current theorem-feasibility verdict

**Go.** M3-B gives a non-atomic sufficient condition for grouped report
correctness. M3-C, under `PsiDeletionMonotonicity`, gives the candidate
converse: grouped correctness implies `GroupSoundness`. Together, for
residually faithful realizations over deletion-monotone reference contracts,
`GroupSoundness` characterizes grouped report correctness. The monotonicity
assumption is substantive and should be tracked explicitly.
