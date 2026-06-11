# M3 Reportability Contract

## 1. Purpose

M3 develops a positive sufficient-condition theory for **contract-relative
repair reportability**.

The central question is:

> When do two implementations of the same reporting contract necessarily
> produce the same grouped minimal-repair report?

The main theorem target is:

> **Lever atomicity suffices for grouped repair invariance.**

This is not a claim that every useful representation must be atomic, or that
atomicity is necessary. It is a theorem about a strong, auditable condition
under which report invariance is guaranteed rather than observed
experimentally.

M1.5 motivates the need for an explicit reporting contract by showing that raw
lever-level repair families need not be canonical. M3 does not restate that
negative existence result as its contribution. It starts after the reporting
contract has been fixed and asks for conditions that make the resulting report
stable.

## 2. Two-Axis Frame

M3 uses two axes.

| Axis | Question | Required output |
| --- | --- | --- |
| **Truth / certificate** | Does each residual instance express the intended problem, and is its SAT/UNSAT claim checkable? | Residual-status agreement, manifests, hashes, and machine-checkable evidence |
| **Repair / report** | Which contract commitments must be removed, and is that answer invariant across implementations? | Minimal contract repairs and a stable grouped report |

The main theorem lies on the repair/report axis. It assumes that the compared
implementations already agree with the same contract on the truth of every
admissible residual problem. It does not infer that agreement from matching
repair output.

Certificate formats may differ across implementations. One realization may use
LRAT replay while another uses a separately audited SAT model or a different
proof-producing solver. M3 requires each claim to remain checkable, but grouped
repair invariance does not require certificate byte identity or proof-log
transport.

## 3. Contract Objects

### 3.1 Reportability contract

A **reportability contract** is a tuple

```text
C = (A, I, Psi, label, report_policy)
```

where:

- `A` is the finite universe of reportable atoms;
- `I subseteq A` is the active atom set for the case under study;
- `Psi(T)` is the reference residual problem for every `T subseteq I`;
- `label(a)` is the stable human-facing identity of atom `a`;
- `report_policy` fixes how implementation-level deletions are mapped to
  contract atoms.

The contract fixes what a report is allowed to say. Examples of reportable
atoms are `unanimity`, `liberalism`, or a deliberately person-specific
commitment. Choosing those atoms is a modeling decision and must precede repair
comparison.

The contract is deletion-closed at the case level: every `T subseteq I` has a
defined residual problem `Psi(T)`. This ensures that minimal repair is evaluated
over a fixed comparison domain. Atoms in `A \ I` are inactive for the case and
do not occur in its contract repairs, raw repairs, or grouped reports.

This note fixes `report_policy` to the **touch-any** policy: an atom is reported
when a repair deletes at least one lever in that atom's implementation block.
The policy is explicit because it is part of the reporting specification, not
an inference from the encoding.

### 3.2 Realization

A **realization** of `C` is a tuple

```text
E = (B, Lambda, beta, phi_E, evidence)
```

where:

- `B` is fixed background structure that is not exposed as repairable;
- `Lambda` is the finite set of repairable implementation levers;
- `beta(a)` is a nonempty block of levers implementing reportable atom `a`;
- the blocks `beta(a)` are pairwise disjoint;
- `Lambda_I = union_{a in I} beta(a)` is the active implementation interface;
- `phi_E(B, U)` is the encoded residual instance for every
  `U subseteq Lambda_I`;
- `evidence(U)` records the evidence and checker metadata for the claimed status
  of an implementation residual.

Here `beta(T) = union_{a in T} beta(a)` is the block-aligned implementation of
the contract residual `T subseteq I`. A realization is
**implementation-deletion-closed** when `phi_E(B, U)` is defined for every
`U subseteq Lambda_I`, including sets that remove only part of a non-atomic
block.

A realization is **residually faithful** when, for every `T subseteq I`,

```text
SAT(phi_E(B, beta(T))) iff SAT(Psi(T)).
```

Residual faithfulness is required only on block-aligned residuals because those
are the implementation images of contract residuals. It is stronger than
agreement on the fully active instance: contract-level minimality depends on
all active-atom subsets. The fully active implementation instance is
`phi_E(B, Lambda_I) = phi_E(B, beta(I))`.

### 3.3 Raw and grouped repairs

For an UNSAT fully active realization, its raw minimal repair family is

```text
RawRep(E) = {
  R subseteq Lambda_I
  | SAT(phi_E(B, Lambda_I \ R))
  and, for every R' proper-subset R,
      UNSAT(phi_E(B, Lambda_I \ R'))
}.
```

Under the contract's touch-any policy, the contract report of a raw repair is:

```text
group_E(R) = {a in I | R intersects beta(a)}.
```

The grouped repair family removes duplicate reports and retains only
inclusion-minimal report sets:

```text
GroupedRep_C(E) =
  Min_subseteq {group_E(R) | R in RawRep(E)}.
```

The reference minimal repair family defined directly by the contract is

```text
ContractRep(C) = {
  G subseteq I
  | SAT(Psi(I \ G))
  and, for every G' proper-subset G, UNSAT(Psi(I \ G'))
}.
```

All three repair objects are case-relative: `ContractRep(C)` and
`GroupedRep_C(E)` range over active atoms `I`, while `RawRep(E)` ranges over
their active implementation interface `Lambda_I`. Inactive atoms and their
levers are outside these domains.

### 3.4 Grouped repair invariance

For a reportability contract `C` and two realizations `E1` and `E2`,
**grouped repair invariance** is the theorem-level predicate

```text
GroupedInvariance(C, E1, E2) :iff
  GroupedRep_C(E1) = ContractRep(C) = GroupedRep_C(E2).
```

`GroupedInvariance` is a property to be proved about a contract and its
realizations. It is not a component of `C`, `E`, `RawRep`, `group_E`, or
`GroupedRep_C(E)`.

### 3.5 Contract-relative lever atomicity

A realization is **lever-atomic relative to `C`** when every reportable atom is
implemented by exactly one repairable lever:

```text
for every a in I, |beta(a)| = 1.
```

Together with the definition of `Lambda_I` and block disjointness, atomicity
makes `beta` a bijection between active contract atoms and active repairable
levers.

Atomicity is relative to the selected contract. A person-specific encoding may
be atomic under a person-specific reporting contract and non-atomic under a
contract that treats liberalism as one indivisible reporting unit. The theorem
therefore does not declare an encoding atomic in isolation.

Fixed Tseitin variables, selector variables, and other non-repairable encoding
machinery belong to `B`; they do not violate lever atomicity. The condition
concerns only the interface through which repairs are permitted and reported.

Under atomicity, the distinction between touch-any and reasonable
intersection-versus-containment variants collapses: touching the singleton
block is the same as deleting the whole block. The theorem therefore remains
about atomic interfaces rather than a taxonomy of reporting policies.

## 4. Main Theorem Target

### Theorem: Atomic report invariance

Let `C = (A, I, Psi, label, report_policy)` be a deletion-closed reportability
contract with `I subseteq A`, the touch-any reporting policy, and fully active
reference problem `Psi(I)` UNSAT. Let `E1` and `E2` be
implementation-deletion-closed, residually faithful realizations of `C`. If
both realizations are lever-atomic relative to `C`, then

```text
GroupedInvariance(C, E1, E2).
```

For each `i` and `a in I`, let `lambda_i(a)` denote the unique element of the
singleton block `beta_i(a)`. Atomicity induces a bijection between the two
active lever interfaces:

```text
h(lambda_1(a)) = lambda_2(a) for every a in I.
```

This atom-induced bijection transports the raw minimal repair family of `E1`
exactly to the raw minimal repair family of `E2`. The raw transport conclusion
depends on atomicity: only then does each active atom identify exactly one
active lever on each side.

### Proof argument

For each realization `Ei`, define

```text
Lambda_i,I = union_{a in I} beta_i(a).
```

Atomicity and block disjointness give a bijection between `G subseteq I` and
`beta_i(G) subseteq Lambda_i,I`. For any `G subseteq I`, residual faithfulness
gives

```text
SAT(Psi(I \ G))
iff SAT(phi_i(B_i, beta_i(I \ G))).
```

Under atomicity and disjoint block coverage of the active interface,

```text
beta_i(I \ G) = Lambda_i,I \ beta_i(G).
```

Because the subset correspondence is bijective, proper subset inclusion is
preserved in both directions. Repair feasibility and inclusion-minimality are
therefore preserved. Hence `beta_i` maps `ContractRep(C)` bijectively to
`RawRep(Ei)`, and touch-any grouping maps that raw family back to
`ContractRep(C)`. Applying the argument to `E1` and `E2` proves grouped
invariance; composing the two atom-lever bijections proves exact raw repair
transport.

### Why this is not circular

`ContractRep(C)` is defined from the reference residual problems `Psi`, whereas
`RawRep(E)` is computed from implementation residuals `phi_E`. Residual
faithfulness is the bridge assumption on the truth/certificate axis, and
atomicity is the interface condition on the repair/report axis. The theorem is
therefore an interface-preservation result. It does not define grouped
invariance by assuming that the two grouped repair families agree.

### What the theorem does not require

The theorem does not require:

- clause-multiset equivalence between `E1` and `E2`;
- identical auxiliary variables or clause counts;
- identical solver traces or certificate formats;
- a claim that atomicity is necessary;
- family-level transfer beyond the declared scope of `C`.

Clause-multiset equivalence remains useful as an engineering control, but the
positive theorem is contract-semantic: residual faithfulness and atomicity are
the operative assumptions.

## 5. Boundary of the Guarantee

If a block `beta(a)` contains several independently removable levers, then a
raw repair may remove only part of the block. The grouped report must then
decide whether touching one implementation component counts as removing the
whole contract atom. Different rules such as `any`, `all`, threshold, or
role-sensitive reporting can produce different answers.

M3 does not call all such representations invalid. It makes the narrower
statement that the atomic case avoids this ambiguity and therefore carries a
general invariance guarantee. Non-atomic contracts may still be invariant, but
that must be established by a separate theorem or by exhaustive evidence for
the declared scope.

Atomicity also does not repair an unfaithful encoding. If two implementations
disagree about the status of some residual problem, the prerequisite on the
truth/certificate axis has failed and the reportability theorem is
inapplicable.

## 6. Connection to M4

M3 proves preservation of grouped repair reporting under atomic repair
interfaces. M4 should analogously prove preservation of governance auditability
under delegation when observability and evidence obligations are inherited.
The structural bridge is the point: M3 concerns repair-report preservation,
whereas M4 concerns auditability-under-delegation preservation.

## 7. Arrow as a Prerequisite Testbed

Arrow must be treated as a structurally different prerequisite testbed, not as
a second example of the Sen experiment.

For a Sen-style application, the program may already have a justified finite
or family-level semantic scope in which the reference residual problems can be
stated. M3 can then test whether implementations realize that same contract
and whether their repair interfaces are atomic.

For an Arrow-style application, finite-to-general transfer in the individual
dimension may fail before repair reportability is reached. The first question
is therefore whether a finite residual contract is a legitimate representative
of the intended Arrow family at all. This is a truth/certificate prerequisite,
not a repair/report comparison.

The Arrow testbed should proceed in this order:

1. State the target family and the finite-model or transfer claim required for
   each admissible residual problem.
2. Prove the transfer claim or mark the precise scope in which it is valid.
3. Establish residual faithfulness for the implementations inside that scope.
4. Only then test lever atomicity and apply the grouped repair theorem.

If the transfer prerequisite fails, the result is a reportability scope wall:
finite grouped repairs may still be reported as finite-case facts, but they
must not be presented as repairs for the unrestricted Arrow family.

## 8. Engineering Obligations

An M3 implementation should emit:

- a contract manifest with stable atom identifiers, labels, scope, and the
  active set `I subseteq A`, plus the reporting policy;
- a realization manifest recording `B`, `Lambda`, `Lambda_I`, every `beta(a)`
  block, and whether deletion closure and the atomicity check pass;
- implementation-residual hashes and SAT/UNSAT status for every queried
  `U subseteq Lambda_I`;
- block-aligned residual comparisons for every `T subseteq I`;
- checker metadata for each claimed status;
- raw repair families, grouped repair families, and `ContractRep(C)`;
- a comparison report showing the theorem assumptions and equality checks;
- explicit scope and transfer fields for any family-level interpretation.

The auditor must reconstruct active-interface coverage, block disjointness,
atomicity, residual status agreement, and repair minimality independently of
the generator.

## 9. M3 Completion Criteria

M3 is complete when:

1. the definitions above are fixed in a machine-readable contract schema;
2. atomicity and residual faithfulness have independent auditors;
3. the main theorem is formalized, preferably in Lean at the finite-set
   abstraction level;
4. at least one atomic pair of realizations demonstrates the positive theorem;
5. at least one non-atomic realization is classified as outside the guarantee,
   without treating non-atomicity itself as proof of divergence;
6. the Arrow testbed records whether the transfer prerequisite succeeds or
   stops the reportability claim at finite scope.

## Appendix A. Preservation Targets

The following targets are an audit checklist, not separate theorem claims.

1. **Semantic truth preservation.** Each residual implementation represents the
   intended residual contract problem.
2. **Status preservation.** SAT/UNSAT status agrees across the reference problem
   and every compared realization.
3. **Certificate preservation.** Every claimed status remains independently
   checkable with recorded checker, provenance, and hashes.
4. **Repair-feasibility preservation.** Every reported repair restores
   satisfiability in the declared scope.
5. **Repair-minimality preservation.** No proper reported subset already
   restores satisfiability.
6. **Report preservation.** Grouped repair identities agree under the fixed
   reportability contract.
