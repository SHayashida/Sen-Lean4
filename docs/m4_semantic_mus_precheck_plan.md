# M4 Semantic MUS Symmetry Precheck Plan

## 1. Purpose

This plan defines a selector-free semantic MUS/MCS precheck before full M4
warrant-contract design.

The question is whether the voter-indexed repair multiplicity observed in
Sen24 survives after replacing the bundled `minlib` selector implementation
with two fixed semantic rights atoms:

```text
right(voter, unordered_alt_pair)
```

If it survives and is equivariant under voter swap, the result supports further
M4 design around semantic MUS/MCS obstruction-shape structure. If it does not,
the project returns to the warrant-contract track without changing M4 scope.

## 2. Target Residuals

The target residuals are the two Sen24 UNSAT residuals in the five-lever atlas:

| Case | Production active levers | Semantic replacement |
| --- | --- | --- |
| `case_11101` | `asymm`, `un`, `minlib`, `no_cycle4` | replace `minlib` by two fixed rights atoms |
| `case_11111` | `asymm`, `un`, `minlib`, `no_cycle3`, `no_cycle4` | replace `minlib` by two fixed rights atoms |

The bit order is the production atlas order:

```text
asymm, un, minlib, no_cycle3, no_cycle4
```

## 3. Semantic Atom Universe

The semantic atom universe for each witness configuration is:

- the active base atoms of the target residual, excluding `minlib`;
- `right(0, P)`;
- `right(1, Q)`;

where `P` and `Q` are unordered alternative pairs from `{0,1,2,3}`.

Pairs are canonicalized by sorting endpoints. Thus `{x,y}` and `{y,x}` are the
same semantic rights atom.

The precheck uses all ordered witness configurations of the form:

```text
((voter0, P), (voter1, Q))
```

There are six unordered alternative pairs, hence `6 * 6 = 36` witness
configurations per target residual.

## 4. Selector-Free Fixed-Witness Encoding

The exploratory encoder must not use:

- `sel0`;
- `sel1`;
- voter-pair selectors;
- role-specific selectors;
- selector-existence clauses.

For an active right atom `right(i,{x,y})`, the clause block states directly that
the social comparison on `{x,y}` follows voter `i` for every profile. If voter
`i` ranks `x` above `y`, the block emits the unit consequence for `x > y`;
otherwise it emits the unit consequence for `y > x`.

Each semantic atom block receives:

- an independent activation guard variable;
- a provenance label;
- a clause count.

The guard variable is not part of the semantic MUS universe. Complete subset
enumeration is over semantic atoms only.

## 5. Complete Enumeration

For every target residual and every witness configuration, enumerate every
subset of the active semantic atom universe.

For each subset, record:

- `SAT`;
- `UNSAT`;
- `UNKNOWN`.

Then compute:

- all inclusion-minimal UNSAT subsets;
- all inclusion-minimal correction/deletion sets;
- all minimal hitting sets of the complete MUS family.

The directly enumerated MCS family must equal the minimal hitting sets of the
complete MUS family. If any subset is `UNKNOWN`, that witness configuration is
not eligible for `PASS`.

## 6. Required Metrics

For each witness configuration, report:

- all semantic MUS;
- all semantic MCS;
- rights support of every MUS;
- intersection of rights atoms across all MUS;
- all minimal rights-only hitting sets;
- whether any MUS contains neither right;
- whether every MUS contains both rights;
- whether only one voter's right is present in every MUS;
- MCS voter-index multiplicity;
- clause provenance counts by semantic atom.

The precheck must inspect MUS-level rights participation directly. Hitting-set
results alone are not sufficient for the symmetry decision.

## 7. O2/O3/O4 Classification

Classify each witness configuration by overlap between the two rights pairs:

- O2: same unordered pair;
- O3: exactly one alternative shared;
- O4: disjoint pairs.

Within each class, compare semantic MUS hypergraphs up to alternative
relabeling. This checks whether the M2 obstruction-shape classes align with the
semantic MUS/repair geometry.

## 8. Pre-Registered Shape Signature

Before executing the precheck, the structural signature used for O2/O3/O4
comparison is fixed as:

```text
ShapeSignature(W) :=
  (
    MUS cardinality multiset,
    MCS cardinality multiset,
    rights participation multiset,
    minimal rights-only hitting-set family,
    MUS hypergraph degree sequence,
    voter-swap stabilizer-subgroup profile of W,
    witness-configuration orbit-size profile under voter swap
  )
```

The Phase 1 run does not fully define the formal report-fiber multiplicity
`mu`. Where the result table records `mu`, it must label it as provisional
voter-indexed semantic repair multiplicity and must not conflate it with a
future report-fiber invariant.

The final two components are diagnostics for the fixed witness configuration
`W`, not for semantic repair objects. Cross-shape `STRONG GO` is primarily
grounded in MUS/MCS structural invariants. Configuration stabilizer and
configuration orbit size are auxiliary symmetry diagnostics. Phase 2 must define
repair objects, repair actions, repair stabilizer subgroups, repair orbits,
report fibers, and report-fiber multiplicity separately.

O2/O3/O4 have different numbers of witness configurations. Therefore aggregate
MUS or repair totals are reference values only. They are not evidence for
STRONG GO. The comparison unit is one of:

- the alternative-relabeling orbit canonical representative;
- the normalized signature for that representative;
- the multiset of representative signatures inside a shape.

Within a shape, representative signatures must be stable under complete
alternative-relabeling search. Across shapes, STRONG GO requires at least one
pre-registered `ShapeSignature` component to differ in a way that is not
explained by witness-configuration count, variable names, selector machinery,
or aggregate totals.

Hypergraph comparison must use canonical labeling or complete relabeling
search. The implementation must not decide isomorphism by raw JSON order.

## 9. Voter-Swap Equivariance

Define voter swap `tau` by exchanging voter `0` and voter `1`.

For each witness configuration `W`, compute `tau(W)` and check:

```text
MUS(tau(W)) = tau(MUS(W))
MCS(tau(W)) = tau(MCS(W))
```

After computing the families, report:

- stabilizer subgroup;
- nonidentity stabilizer elements;
- witness-configuration orbit size `1` or `2`.

Do not confuse a nontrivial stabilizer subgroup with a nontrivial
witness-configuration orbit.

## 10. Gate Criteria

### STRONG GO

All of the following must hold:

- selector-free fixed-witness packages reproduce expected UNSAT status;
- no MUS omits both rights;
- complete MUS/MCS duality passes;
- voter-swap equivariance passes;
- alternative-relabeling checks pass within O2/O3/O4 classes;
- semantic voter-indexed repair multiplicity survives;
- the multiplicity is not created by selector clauses.
- within each O2/O3/O4 class, representative signatures are stable under
  alternative relabeling;
- across O2/O3/O4 shapes, at least one pre-registered `ShapeSignature`
  component differs;
- the observed difference is not just witness-configuration count, variable
  naming, selector machinery, or an aggregate count.

STRONG GO means the repair geometry is not merely voter-swap symmetric. It is
evidence that repair geometry depends structurally on the M2 O2/O3/O4
obstruction shape.

### WEAK GO / CONDITIONAL GO

Semantic multiplicity and voter-swap equivariance survive, but one of the
following holds:

- O2/O3/O4 have the same `ShapeSignature`;
- observed differences reduce to voter swap, naming, configuration count, or
  aggregate count;
- shape differences exist but representative signatures are not stable enough
  to support a finite classification.

In this case, the two-voter result is not enough to approve an
orbit-identifiability flagship. The next authorized work is only a separate
two-voter repair-orbit and report-fiber precheck design. Warrant theorem work,
Lean formalization, paper-claim promotion, and three-voter extension remain
prohibited.

### NO-GO

Any of the following is sufficient:

- semantic multiplicity disappears;
- a rights-free MUS exists;
- equivariance fails;
- selector-free encoding does not reproduce the phenomenon;
- MUS/MCS duality fails;
- the result reduces only to duplicated implementation blocks;
- `UNKNOWN` prevents complete classification.
- semantic multiplicity is explained entirely by duplicated rights blocks and
  has no connection to obstruction shape;
- no meaningful structural invariant exists for shape comparison, and no
  theory hypothesis can be formed for a Phase 2 repair-orbit/report-fiber
  precheck.

### Interpretation Discipline

- A shape-dependent `mu` difference is a candidate sufficient signal for
  STRONG GO, but it is not required.
- If `mu` is constant, other pre-registered structural invariants may still
  justify STRONG GO.
- A `mu` difference alone is not STRONG GO evidence unless it is a normalized
  representative-level difference.
- Voter-swap equivariance alone says only that the construction respects voter
  symmetry.
- Both same-shape stability and cross-shape structural difference are required
  for STRONG GO.

Authorized sequence:

```text
Phase 1: Semantic MUS/MCS obstruction-shape gate
Phase 2: Two-voter repair-orbit and report-fiber gate
Phase 3: Three-voter S3 extension, only after Phase 2 GO
Phase 4: Dedicated M4 scope decision
Phase 5: Warrant envelope and delegated-warrant work
```

## 11. Execution and Outputs

Temporary outputs are written under:

```text
/tmp/sen_m4_semantic_mus/
```

Repository outputs are limited to:

- `docs/m4_mus_orbit_gate_decision.md`;
- `docs/m4_semantic_mus_precheck_plan.md`;
- exploratory scripts under `scripts/exploration/m4/`;
- `docs/m4_semantic_mus_precheck_result.md`.

Required validation:

- `python -m py_compile` on new scripts;
- focused deterministic tests for pair canonicalization;
- focused tests for voter swap;
- focused tests for MUS minimality;
- focused tests for MCS/MUS hitting-set duality;
- `git diff --check`.

No expensive unrelated CI is part of this plan.
