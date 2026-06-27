# M4 Semantic MUS Orbit Gate Decision

## 1. Decision

Delegated Warrant Preservation implementation is temporarily on hold.

The current M4 scope is not changed by this document. Before beginning the full
warrant-contract design, the project will run a pre-M4 mathematical gate:
evaluate whether the voter-indexed repair multiplicity observed in Sen24 is
already present at the level of semantic rights atoms, semantic MUS/MCS
structure, and the natural voter-swap symmetry.

This is a STRONG GO TO PHASE 2 REPAIR-ORBIT ANALYSIS / WEAK GO /
CONDITIONAL GO / NO-GO gate for directing pre-M4 work. It is not an M4 theorem,
not a Lean formalization, and not a change to the dissertation scope.

## 2. Gate Question

The gate asks whether the Sen24 repair multiplicity is caused by semantic
right atoms and their MUS/MCS orbit structure, rather than by implementation
selector machinery.

The precheck must therefore use selector-free fixed-witness packages. The MUS
universe is semantic:

- `asymm`;
- `un`;
- `no_cycle3`;
- `no_cycle4`;
- `right(voter, unordered_alt_pair)`.

CNF clauses are not MUS atoms. Assumption guards may be used to activate clause
blocks, but guard variables are not semantic atoms.

## 3. Scope Discipline

This decision does not authorize changes to:

- production encoding;
- `SocialChoiceAtlas/**/*.lean`;
- M1-M3 theorem statements;
- `Certificates/**`;
- tracked `results/**`;
- paper manuscripts;
- existing claim boundaries;
- the doctoral scope lock.

New work is limited to:

- this decision document;
- `docs/m4_semantic_mus_precheck_plan.md`;
- exploratory scripts under `scripts/exploration/m4/`;
- temporary execution outputs under `/tmp/sen_m4_semantic_mus/`;
- the result document `docs/m4_semantic_mus_precheck_result.md`.

## 4. Gate Outcomes

### STRONG GO TO PHASE 2 REPAIR-ORBIT ANALYSIS

If the semantic precheck shows selector-free multiplicity, MUS/MCS duality,
voter-swap equivariance, same-shape representative stability, and structural
O2/O3/O4 shape dependence, then a separate two-voter repair-orbit and
report-fiber precheck is authorized.

This does not establish repair orbits, report fibers, orbit identifiability, or
M4 warrant semantics.

### WEAK GO / CONDITIONAL GO

If semantic multiplicity and voter-swap equivariance survive, but O2/O3/O4
shape signatures are identical or unstable, then the two-voter result is not
enough to approve an orbit-identifiability flagship. The next authorized work is
only a separate two-voter repair-orbit and report-fiber precheck design.

### NO-GO

If selector-free semantic packages do not reproduce the phenomenon, or if the
result reduces to duplicated implementation blocks, the project returns to the
warrant-contract track without changing M4 scope.

## 5. Phase 1 Completion Status

Phase 1 verdict:

```text
STRONG GO TO PHASE 2 REPAIR-ORBIT ANALYSIS
```

Phase 1 established obstruction-shape-dependent semantic MUS/MCS structure.

Phase 1 did not establish:

- repair orbit;
- repair stabilizer;
- report fiber;
- formal report-fiber multiplicity;
- orbit identifiability;
- any M4 scope change.

Phase 2 is the only newly authorized theoretical task:

```text
A separate two-voter Obstruction-Indexed Repair-Orbit and Report-Fiber Precheck.
```

Current doctoral scope remains unchanged. Delegated Warrant Preservation remains
provisional and paused. M4 scope will be reconsidered only after Phase 2 review.

The correct order is:

```text
Phase 1: Semantic MUS/MCS obstruction-shape gate
Phase 2: Two-voter repair-orbit and report-fiber gate
Phase 3: Three-voter S3 extension, only after Phase 2 GO
Phase 4: Dedicated M4 scope decision
Phase 5: Warrant envelope and delegated-warrant work
```

## 6. Non-Claims

This gate makes no claim about:

- Arrow;
- Gibbard-Satterthwaite;
- general social-choice theorem families;
- family-level CNF/LRAT/atlas transfer;
- M4 warrant semantics;
- Lean formalization of MUS/MCS orbit structure.
