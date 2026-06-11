# M3 Atomicity Theorem Skeleton

## 1. Purpose and Theorem Target

This note turns the definitions in
[`docs/m3_reportability_contract.md`](m3_reportability_contract.md) into a
proof-ready theorem skeleton. It introduces no new experimental or application
scope.

The target implication is:

```text
RepairAtomicity + ResidualFaithfulness
  => GroupedRepairInvariance.
```

More precisely, for a deletion-closed reportability contract `C` and two
implementation-deletion-closed realizations `E1` and `E2`:

```text
RepairAtomicity(E1, C)
and RepairAtomicity(E2, C)
and ResidualFaithfulness(E1, C)
and ResidualFaithfulness(E2, C)
=> GroupedInvariance(C, E1, E2).
```

The fully active reference problem is assumed UNSAT so that the minimal repair
families are the intended repair objects.

## 2. Dependency Graph

```text
C
|
v
E
|
v
RawRep(E)
|
v
group_E
|
v
GroupedRep_C(E)
|
v
GroupedInvariance(C, E1, E2)
```

The dependencies mean:

1. `C` fixes the active reportable atoms, reference residuals, labels, and
   grouping policy.
2. `E` realizes `C` through implementation lever blocks and implementation
   residuals.
3. `RawRep(E)` is computed over active implementation-lever deletions.
4. `group_E` maps each raw deletion to active contract atoms.
5. `GroupedRep_C(E)` minimizes the resulting contract-level reports.
6. `GroupedInvariance` compares two grouped families with the reference
   contract repair family.

`GroupedInvariance` is a theorem-level predicate. It is not a component of
`C`, `E`, `RawRep`, `group_E`, or `GroupedRep_C(E)`.

## 3. Required Definitions

Let:

```text
C = (A, I, Psi, label, report_policy)
```

with `I subseteq A`, deletion-closed reference residuals `Psi(T)` for every
`T subseteq I`, and the touch-any reporting policy.

Let a realization be:

```text
E = (B, Lambda, beta, phi_E, evidence)
```

with pairwise-disjoint nonempty blocks `beta(a)` and active implementation
interface:

```text
Lambda_I = union_{a in I} beta(a).
```

The realization is implementation-deletion-closed when `phi_E(B, U)` is
defined for every `U subseteq Lambda_I`.

### 3.1 Contract repair family

```text
ContractRep(C) = {
  G subseteq I
  | SAT(Psi(I \ G))
  and, for every G' proper-subset G, UNSAT(Psi(I \ G'))
}.
```

### 3.2 Raw implementation repair family

```text
RawRep(E) = {
  R subseteq Lambda_I
  | SAT(phi_E(B, Lambda_I \ R))
  and, for every R' proper-subset R,
      UNSAT(phi_E(B, Lambda_I \ R'))
}.
```

### 3.3 Grouping map

Under the touch-any policy:

```text
group_E(R) = {a in I | R intersects beta(a)}.
```

### 3.4 Grouped implementation repair family

```text
GroupedRep_C(E) =
  Min_subseteq {group_E(R) | R in RawRep(E)}.
```

### 3.5 Repair atomicity

```text
RepairAtomicity(E, C) :iff
  for every a in I, |beta(a)| = 1.
```

This is contract-relative: it applies only to active reportable atoms and their
active implementation interface.

### 3.6 Residual faithfulness

```text
ResidualFaithfulness(E, C) :iff
  for every T subseteq I,
    SAT(phi_E(B, beta(T))) iff SAT(Psi(T)).
```

Here:

```text
beta(T) = union_{a in T} beta(a).
```

### 3.7 Grouped repair invariance

```text
GroupedInvariance(C, E1, E2) :iff
  GroupedRep_C(E1) = ContractRep(C) = GroupedRep_C(E2).
```

## 4. Lemma Chain

### Lemma 1: Active-domain well-formedness

**Statement.** For every realization `E` of `C`:

```text
beta(T) subseteq Lambda_I for every T subseteq I,
```

and all sets occurring in `ContractRep(C)`, `RawRep(E)`, and
`GroupedRep_C(E)` remain inside `I` or `Lambda_I` as appropriate.

**Assumptions used.**

- `I subseteq A`;
- `Lambda_I = union_{a in I} beta(a)`;
- `phi_E(B, U)` is defined for every `U subseteq Lambda_I`;
- `group_E` quantifies only over `a in I`.

**Proof idea.** Union monotonicity gives `beta(T) subseteq beta(I) = Lambda_I`.
The remaining domain facts follow directly from the bounded set
comprehensions in the repair definitions.

**Lean formalizability.** Yes. This is elementary finite-set membership and
union reasoning.

### Lemma 2: Atomic beta bijection

**Statement.** If `RepairAtomicity(E, C)` holds, then each `a in I` has a unique
active lever `lambda_E(a) in beta(a)`, and:

```text
lambda_E : I -> Lambda_I
```

is a bijection. Consequently, the map:

```text
G |-> beta(G)
```

is a bijection between subsets of `I` and subsets of `Lambda_I`.

**Assumptions used.**

- pairwise disjointness of `beta(a)`;
- nonemptiness of every active block;
- `RepairAtomicity(E, C)`;
- definition of `Lambda_I`.

**Proof idea.** Atomicity turns each nonempty block into a singleton.
Disjointness makes the selected lever map injective, and active-interface
coverage makes it surjective. The induced powerset map is therefore bijective.

**Lean formalizability.** Yes. Use finite-set cardinality-one lemmas and the
bijection induced on finite powersets.

### Lemma 3: Complement identity

**Statement.** If `RepairAtomicity(E, C)` holds, then for every
`G subseteq I`:

```text
beta(I \ G) = Lambda_I \ beta(G).
```

**Assumptions used.**

- Lemma 2;
- pairwise disjoint active blocks;
- `Lambda_I = beta(I)`.

**Proof idea.** Under the atomic bijection, membership in `beta(G)` is exactly
membership of the corresponding atom in `G`. Taking complements on the two
finite active domains therefore commutes with `beta`.

**Lean formalizability.** Yes. An extensional proof over lever membership is
direct.

### Lemma 4: Feasibility transfer

**Statement.** If `RepairAtomicity(E, C)` and
`ResidualFaithfulness(E, C)` hold, then for every `G subseteq I`:

```text
SAT(Psi(I \ G))
iff SAT(phi_E(B, Lambda_I \ beta(G))).
```

Thus `G` is a contract-level repair candidate iff `beta(G)` is an
implementation-level repair candidate.

**Assumptions used.**

- residual faithfulness at `T = I \ G`;
- Lemma 3.

**Proof idea.** Residual faithfulness gives equivalence with
`phi_E(B, beta(I \ G))`. Rewrite that active lever set using the complement
identity.

**Lean formalizability.** Yes, provided SAT status is represented abstractly as
a predicate on residual problems. No SAT solver formalization is needed for
this finite-set theorem.

### Lemma 5: Minimality transfer

**Statement.** Under the assumptions of Lemma 4:

```text
G in ContractRep(C) iff beta(G) in RawRep(E).
```

**Assumptions used.**

- Lemma 2;
- Lemma 4;
- inclusion-minimal definitions of `ContractRep` and `RawRep`.

**Proof idea.** Lemma 4 transfers repair feasibility. Lemma 2 preserves and
reflects strict subset inclusion:

```text
G' proper-subset G
iff beta(G') proper-subset beta(G).
```

Every strict subset of `beta(G)` is block-aligned under atomicity, so residual
faithfulness covers every subset needed by raw minimality.

**Lean formalizability.** Yes. The proof is finite-set order isomorphism plus
predicate rewriting.

### Lemma 6: Grouping inverse under atomicity

**Statement.** If `RepairAtomicity(E, C)` holds, then for every
`G subseteq I`:

```text
group_E(beta(G)) = G.
```

Furthermore, every `R subseteq Lambda_I` satisfies:

```text
beta(group_E(R)) = R.
```

**Assumptions used.**

- touch-any reporting policy;
- Lemma 2;
- pairwise-disjoint singleton blocks.

**Proof idea.** A singleton block intersects `beta(G)` exactly when its atom is
in `G`. Conversely, each active lever belongs to the unique singleton block of
its corresponding atom.

**Lean formalizability.** Yes. Both identities follow by finite-set
extensionality.

### Lemma 7: Single-realization report correctness

**Statement.** If `RepairAtomicity(E, C)` and
`ResidualFaithfulness(E, C)` hold, then:

```text
GroupedRep_C(E) = ContractRep(C).
```

**Assumptions used.**

- Lemma 5;
- Lemma 6;
- definitions of grouped and contract repair families.

**Proof idea.** Lemma 5 identifies the raw repair family as the image of
`ContractRep(C)` under `beta`. Lemma 6 maps every such raw repair back to its
unique contract repair. Since `ContractRep(C)` is already
inclusion-minimal, the final `Min_subseteq` operation removes nothing except
possible duplicate presentations, of which atomicity permits none.

**Lean formalizability.** Yes. The main obligation is a small lemma showing
that taking inclusion-minimal elements of an already minimal family returns
the same family.

### Theorem M3-A: Atomic grouped repair invariance

**Statement.** Let `C` be deletion-closed with `I subseteq A`, touch-any
reporting, and `Psi(I)` UNSAT. Let `E1` and `E2` be
implementation-deletion-closed realizations. If:

```text
RepairAtomicity(E1, C)
and RepairAtomicity(E2, C)
and ResidualFaithfulness(E1, C)
and ResidualFaithfulness(E2, C),
```

then:

```text
GroupedInvariance(C, E1, E2).
```

Equivalently:

```text
GroupedRep_C(E1) = ContractRep(C) = GroupedRep_C(E2).
```

**Assumptions used.**

- Lemma 7 for `E1`;
- Lemma 7 for `E2`;
- the definition of `GroupedInvariance`.

**Proof idea.** Apply single-realization report correctness independently to
both realizations and compose the two equalities through `ContractRep(C)`.

**Lean formalizability.** Yes. Once Lemma 7 is available, the theorem is an
equality transitivity argument.

### Corollary: Raw repair transport under the atom-induced bijection

**Statement.** Under the assumptions of Theorem M3-A, let
`lambda_i(a)` be the unique lever in `beta_i(a)`. Define:

```text
h(lambda_1(a)) = lambda_2(a).
```

Then `h` is a bijection between `Lambda_1,I` and `Lambda_2,I`, and its
powerset action transports raw repairs exactly:

```text
{h(R) | R in RawRep(E1)} = RawRep(E2).
```

**Assumptions used.**

- Lemma 2 for both realizations;
- Lemma 5 for both realizations;
- Theorem M3-A assumptions.

**Proof idea.** Each raw repair is uniquely `beta_1(G)` for some
`G in ContractRep(C)`. The atom-induced bijection maps it to `beta_2(G)`,
which is exactly the corresponding raw repair of `E2`. The converse follows
symmetrically.

**Lean formalizability.** Yes. Define `h` as the composition of the two atomic
bijections and lift it to finite sets.

## 5. Where the Theorem Would Fail

- **Non-atomic block allows partial deletion.** An arbitrary raw repair need
  not be block-aligned, so residual faithfulness does not determine its status
  and grouping need not invert `beta`.
- **Residual faithfulness fails.** Contract residual status and implementation
  residual status can diverge, invalidating feasibility transfer.
- **Inactive atoms/levers are accidentally included.** The powerset
  correspondence no longer uses the same active domains, so the bijection and
  complement identity can fail.
- **Grouping policy is changed without updating the contract.** The
  theorem would prove correctness for a policy different from the one used to
  produce reports.

## 6. Relation to M1.5

- **M1.5:** without an adequate reportability condition, raw repair reporting
  can fail even under `≡CM`.
- **M3:** under atomicity and residual faithfulness, grouped repair reporting
  is recovered.
- **Boundary:** M3 does not reprove RENI. It provides a positive sufficient
  condition for a different, contract-relative invariance property.
