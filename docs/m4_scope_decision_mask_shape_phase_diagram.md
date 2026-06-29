# M4 Scope Decision: Mask-Shape Phase Diagram

Status: scope-decision note / precheck-supported candidate

Depends on: M4 mask-shape collapse law audit

Current authorization: theorem-scope decision only

Not authorized: Lean theorem, Certificate 2 completion, 3-voter run,
warrant-contract implementation, paper-claim promotion

## 1. Decision

Decision:
Do not freeze M4 Theorem C at the ALL_W_UNSAT-only mask level.

Instead, register a stronger theorem candidate:

```text
Mask-Shape Collapse Law:
for every bundled residual mask T and obstruction shape s,
if Cell(T,s) is an UNSAT cell, then
  every cell-indexed grouped-report fiber is exactly one repair orbit,
  and every shape-blind report satisfies
    blind_orbit_count(T,report) = |ShapeSupport_UNSAT(T,report)|.
```

ALL_W_UNSAT masks are the special case where all three shapes are UNSAT cells.
MIXED masks are support-truncated cases where only some shapes are UNSAT cells.

This is a candidate theorem supported by the audit. It is not a Lean theorem
or a paper claim.

## 2. Superseded Narrow Reading

The earlier ALL_W_UNSAT-only reading was safe before MIXED-cell repair
geometry was audited.
It is now too narrow because the mask-shape audit passes and MIXED UNSAT
cells satisfy the same collapse law.

The previous reading was not wrong. It was a conservative interim scope.

## 3. New Analysis Unit

The new analysis unit is:

```text
Cell(T,s) := { W inside T | Shape(W)=s }.
```

The ambient residual theory `T` remains a bundled residual mask/schema.
The shape coordinate is computed from the internal witness configuration `W`.
The pair `(T,s)` is an analysis stratum inside `T`; it is not a new ambient
theory identity.

The audit target is:

```text
UNSAT cells = { (T,s) | cell_status(T,s) = ALL_UNSAT }.
```

Repair geometry is defined only on these UNSAT cells. SAT cells contribute no
repair objects.

## 4. Theorem Candidate

Candidate: Mask-Shape Collapse Law.

For every bundled residual mask `T`, obstruction shape `s`, and grouped report
`rho`, if `Cell(T,s)` is an UNSAT cell, then:

```text
Fiber(T,s,rho) is either empty or exactly one G-orbit.
```

Here:

```text
G = S2_voters x S4_alternatives
q_atom(right(voter,P)) = minlib
q_atom(base_atom) = base_atom
```

For every shape-blind report `rho` over the UNSAT cells of `T`:

```text
#Orbits(BlindFiber_UNSAT(T,rho))
=
|ShapeSupport_UNSAT(T,rho)|.
```

The audit result is:

```text
UNSAT cells = 18
UNSAT witness instances = 216
repair objects = 816
repair orbits = 46
cell report fibers = 46
shape-blind fibers = 33
support truncation law = PASS
```

## 5. Consequence for Certificate 2

Certificate 2 should be redesigned as a complete mask-shape phase-diagram
certificate, not as an ALL_W_UNSAT-only certificate.

Certificate 2 should cover all minlib-active cells:

```text
16 minlib-active bundled masks x 3 obstruction shapes = 48 cells.
```

It must not redefine `T` as `(T,s)`.
The cell coordinate is an analysis stratum inside `T`.

Certificate 2 should verify, for each UNSAT cell:

- repair object universe for UNSAT witness instances only;
- group action well-definedness under `S2 x S4`;
- `q`-invariance;
- cell-indexed orbit-fiber exactness;
- absence of partial orbit fragments;
- orbit-stabilizer;
- shape-blind support truncation over the UNSAT support of each mask.

Certificate 2 should also verify, for each SAT cell:

- repair object universe is empty;
- no repair object is created for any SAT witness instance;
- `RepairEmpty(T,s)` holds as a phase-diagram completeness condition.

## 6. Non-Circularity Guard

The scope decision must preserve the following guardrails:

- `T` is a bundled residual mask/schema.
- `T` is not `(mask,W)`.
- `T` is not `(mask,shape)`.
- `Shape(W)` is computed from the internal witness `W`.
- `ResidualClass` is not defined by the collapse law.
- `ResidualClass` is not defined by shape-support stability.
- SAT cells are outside the repair-object universe because they have no UNSAT
  witness repair target, not because they would violate a theorem.

## 7. Relation to MIXED Residuals

The audit changes the interpretation of `MIXED` masks.

Under the old T-only full-mask reading, a `MIXED` mask had no uniform repair
geometry because some witnesses were SAT and others were UNSAT.

Under the mask-shape phase diagram, this is support truncation:

```text
some shape cells are SAT and drop out;
remaining UNSAT shape cells have the same orbit-fiber exactness law.
```

Thus `MIXED` masks are not repair-geometry failures. They are masks whose
UNSAT support is a proper subset of `{O2,O3,O4}`.

## 8. Relation to Arrow / Non-Symmetric Questions

This does not prove Arrow transfer.
However, it shows inside Sen24 that the method can distinguish:

```text
uniform impossibility regimes;
support-truncated mixed regimes;
and repair geometry on each UNSAT cell.
```

This is relevant to future non-symmetric impossibility settings, but no Arrow
or GS theorem is claimed.

## 9. Non-Claims

This decision does not claim:

- Lean theorem;
- Certificate 2 completion;
- paper-ready theorem;
- 3-voter theorem;
- Arrow theorem;
- Gibbard-Satterthwaite theorem;
- general social-choice theorem;
- warrant-contract semantics;
- that shape is part of ambient theory identity;
- that SAT cells have repair objects;
- that MIXED masks have full-mask repair geometry under the old T-only
  reading.

## 10. Next Authorized Action

The next authorized action is to review this scope decision.

If accepted, implement Certificate 2 as a finite data certificate over the
complete 48-cell phase diagram, while preserving `T` as bundled mask/schema
identity. Do not implement Lean theorem promotion until the finite certificate
design is approved.

## Certificate 2 Design Update

Certificate 2 should certify the complete 48-cell phase diagram:

- UNSAT cells: repair geometry and collapse law.
- SAT cells: repair-empty condition.
- MIXED_WITHIN_SHAPE or UNKNOWN cells: failure or conditional status.

This keeps the Mask-Shape Collapse Law from being merely an UNSAT-cell theorem
detached from the full phase diagram.
