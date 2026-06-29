# M4 Certificate Pipeline Consolidation

Status: pipeline-design / docs-only
Depends on: Certificate 2 phase-diagram design
Current authorization: certificate pipeline consolidation only
Not authorized: checker implementation, solver rerun, Lean theorem, 3-voter run, warrant-contract implementation, paper-claim promotion

## 1. Decision

Decision:
Certificate 3 and Certificate 4 are absorbed into Certificate 2 as internal
subchecks.

They are not deleted conceptually.
They are retired as independent downstream stages because Certificate 2 is now
a complete 48-cell phase-diagram certificate.

## 2. Previous Four-Layer Plan

The previous plan was:

```text
Certificate 1:
  ResidualClass / bundled-mask coverage.

Certificate 2:
  Orbit-fiber exactness.

Certificate 3:
  Shape-blind collapse.

Certificate 4:
  Report-shape support collapse law.
```

This plan was appropriate before the Mask-Shape Collapse Law audit
generalized the scope from ALL_W_UNSAT masks to all UNSAT analysis cells.

## 3. Reason for Consolidation

The Mask-Shape Collapse Law audit showed that the relevant finite object is
the 48-cell mask x obstruction-shape phase diagram.

Once Certificate 2 is redesigned over the complete phase diagram, it must
already verify:

- SAT-cell RepairEmpty;
- UNSAT-cell orbit-fiber exactness;
- shape-blind support truncation;
- non-circularity.

Therefore the old Certificate 3 and Certificate 4 checks are no longer
downstream stages.
They are necessary subchecks inside Certificate 2.

## 4. New Pipeline

The consolidated pipeline is:

```text
Certificate 1:
  Bundled-mask coverage and cell-status phase diagram.
  Outputs all 48 cell statuses.

Certificate 1b:
  Exploratory Mask-Shape Collapse Law audit.
  Confirms support truncation and orbit-fiber exactness over all UNSAT cells.

Certificate 2:
  Complete phase-diagram certificate.
  Verifies:
    - all 48 cells are covered;
    - ALL_SAT cells satisfy RepairEmpty;
    - ALL_UNSAT cells satisfy orbit-fiber exactness;
    - shape-blind support truncation holds over UNSAT support;
    - non-circularity conditions hold.
```

There is no independent Certificate 3 or Certificate 4 implementation stage
after this consolidation unless a later scope decision reintroduces them for a
different purpose.

## 5. What Happened to Certificate 3

Old Certificate 3, Shape-Blind Collapse, is absorbed into Certificate 2.

In the new design, shape-blind fibers are evaluated over UNSAT support:

```text
BlindFiber_UNSAT(T,rho)
```

Certificate 2 must report:

```text
shape_blind_fiber_count
blind_orbit_count
shape_support_count
support_truncation_law_holds
```

## 6. What Happened to Certificate 4

Old Certificate 4, Report-Shape Support Collapse Law, is absorbed into
Certificate 2.

The support law becomes the Certificate 2 subcheck:

```text
#Orbits(BlindFiber_UNSAT(T,rho))
=
|ShapeSupport_UNSAT(T,rho)|
```

This is not a separate downstream certificate.
It is part of the phase-diagram certificate.

## 7. Certificate 2 Subchecks

Required Certificate 2 subchecks:

```text
C2.1 Cell coverage:
  all 48 minlib-active mask-shape cells are covered.

C2.2 Cell status:
  ALL_UNSAT = 18
  ALL_SAT = 30
  MIXED_WITHIN_SHAPE = 0
  UNKNOWN = 0
  or any deviation is explicitly reported.

C2.3 SAT-cell RepairEmpty:
  every ALL_SAT cell has no repair objects.

C2.4 UNSAT-cell orbit-fiber exactness:
  every nonempty cell-indexed grouped-report fiber is exactly one complete
  repair orbit.

C2.5 Orbit-stabilizer:
  |Orb(x)| * |Stab(x)| = 48 for every repair object.

C2.6 Shape-blind support truncation:
  #Orbits(BlindFiber_UNSAT(T,rho))
  =
  |ShapeSupport_UNSAT(T,rho)|.

C2.7 Non-circularity:
  T remains bundled mask/schema;
  (T,s) remains an analysis cell;
  ResidualClass is not defined by collapse behavior.
```

## 8. Active RepairEmpty Verification Requirement

Certificate 2 must actively verify RepairEmpty for SAT cells.

It is not enough to skip repair-object generation for SAT cells and then
declare the repair universe empty.
The checker must confirm that each SAT cell is SAT at the fixed-witness
semantic level and that the repair-object constructor is guarded by UNSAT
status.

The checker must not treat the empty deletion as a repair object for SAT
cells.
RepairObject(T,W,R) is defined only when the full fixed-witness theory is
UNSAT.
For SAT cells, RepairEmpty means:

```text
the full fixed-witness theories are SAT;
no UNSAT repair target exists;
no RepairObject is created.
```

This distinguishes active verification from passive non-generation.

## 9. Non-Circularity Guard

The checker must verify or record:

- `T` is a bundled residual mask/schema;
- `Shape(W)` is computed from `W`;
- `Cell(T,s)` is an analysis stratum;
- SAT cells are empty because their fixed-witness theories are SAT;
- UNSAT cells are included because their fixed-witness theories are UNSAT;
- `ResidualClass` is not defined by collapse law, shape support, or orbit
  behavior.

## 10. Non-Claims

This consolidation does not claim:

- Certificate 2 implementation;
- Lean theorem;
- paper-ready theorem;
- general Sen theorem;
- Arrow theorem;
- Gibbard-Satterthwaite theorem;
- 3-voter theorem;
- family-scale theorem;
- warrant-contract semantics;
- semantic-to-CNF correctness theorem;
- that Certificate 3/4 were wrong;
- that shape is part of ambient theory identity.

## 11. Next Authorized Action

The next authorized action is review of the consolidated M4 certificate
pipeline.

If accepted, a future checker design or implementation should target
Certificate 2 as the complete finite-data certificate for the 48-cell
phase diagram. No checker implementation, solver rerun, Lean theorem work,
3-voter work, warrant-contract implementation, or paper-claim promotion is
authorized by this document.
