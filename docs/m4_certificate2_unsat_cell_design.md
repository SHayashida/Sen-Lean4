# M4 Certificate 2 Design: UNSAT-Cell Exactness and SAT-Cell Emptiness

Status: certificate-design / docs-only
Depends on: Mask-Shape Collapse Law audit result
Current authorization: Certificate 2 design only
Not authorized: checker implementation, solver rerun, Lean theorem, 3-voter run, warrant-contract implementation, paper-claim promotion

## 1. Purpose

Certificate 2 is redesigned as a certificate over the mask x
obstruction-shape phase diagram.

It does not certify only the two ALL_W_UNSAT masks.
It certifies the full cell partition:

- UNSAT cells, where repair geometry is defined and orbit-fiber exactness is
  checked;
- SAT cells, where repair objects are empty because there is no inconsistency
  to repair.

The goal is to support the Mask-Shape Collapse Law as a precheck-supported
theorem candidate, not to promote it to a Lean theorem or paper-ready claim.

## 2. Inputs

Certificate 2 design expects the following local generated audit artifacts as
inputs:

```text
/tmp/sen_m4_residual_class_coverage_certificate/mask_statuses.csv
/tmp/sen_m4_residual_class_coverage_certificate/witness_statuses.csv
/tmp/sen_m4_mask_shape_collapse_law_audit/cell_statuses.csv
/tmp/sen_m4_mask_shape_collapse_law_audit/repair_objects.csv
/tmp/sen_m4_mask_shape_collapse_law_audit/cell_report_fibers.csv
/tmp/sen_m4_mask_shape_collapse_law_audit/repair_orbits.csv
/tmp/sen_m4_mask_shape_collapse_law_audit/shape_blind_fibers.csv
/tmp/sen_m4_mask_shape_collapse_law_audit/support_truncation.csv
/tmp/sen_m4_mask_shape_collapse_law_audit/mask_shape_collapse_certificate.json
```

These files are not required to be tracked in git. They are local generated
audit outputs.

## 3. Phase Diagram Domain

Definitions:

```text
BundledMask T:
  a 5-bit bundled residual mask over
    asymm, un, minlib, no_cycle3, no_cycle4.

Shape s:
  one of O2, O3, O4.

Cell(T,s):
  { W inside T | Shape(W)=s }.
```

Expected full phase diagram size:

```text
minlib-active bundled masks: 16
shapes per minlib-active mask: 3
total cells: 48
```

Current audited cell status counts:

```text
ALL_UNSAT = 18
ALL_SAT = 30
MIXED_WITHIN_SHAPE = 0
UNKNOWN = 0
```

## 4. Ambient Theory and Cell Discipline

T remains individuated by bundled residual mask/schema.
Shape is not part of T identity.
W is internal to T.
Shape(W) is computed from W.
Cell(T,s) is an analysis stratum inside T, not a new ambient residual theory.

Forbidden:

```text
T := (mask,W)
T := (mask,shape)
ResidualClass := cells satisfying the collapse law
ResidualClass := shape-support-stable cells
```

Allowed:

```text
Cell(T,s) := { W inside T | Shape(W)=s }
Repair geometry is evaluated on UNSAT cells.
```

## 5. Cell Status Predicates

Define:

```text
CellStatus(T,s) in {
  ALL_UNSAT,
  ALL_SAT,
  MIXED_WITHIN_SHAPE,
  UNKNOWN
}
```

Meanings:

```text
ALL_UNSAT:
  every W in Cell(T,s) is UNSAT.

ALL_SAT:
  every W in Cell(T,s) is SAT.

MIXED_WITHIN_SHAPE:
  some W in Cell(T,s) is SAT and some W is UNSAT.

UNKNOWN:
  at least one W in Cell(T,s) is UNKNOWN.
```

Current Certificate 2 design should proceed only under:

```text
No UNKNOWN cells.
No MIXED_WITHIN_SHAPE cells.
```

If either appears in a future run, Certificate 2 must fail or become
conditional.

## 6. Repair Object Predicate

Define:

```text
RepairObject(T,W,R)
```

only when:

```text
W in Cell(T,s)
CellStatus(T,s) = ALL_UNSAT
R is a semantic MCS / minimal repair for the selector-free fixed-witness
  theory determined by (T,W).
```

RepairObject is undefined or false for SAT cells.
Repair objects are never created for SAT witness instances.
Repair objects are never created to make a theorem true; they are created only
where the fixed-witness semantic theory is UNSAT.

## 7. SAT-Cell Repair-Empty Predicate

SAT-cell emptiness is a first-class part of Certificate 2.

Define:

```text
RepairEmpty(T,s) iff
  CellStatus(T,s) = ALL_SAT
  and there exists no RepairObject(T,W,R) with W in Cell(T,s).
```

SAT cells are part of the complete phase diagram.
They are not ignored.
They certify the empty side of the repair geometry:

```text
no inconsistency, no repair object.
```

Required certificate condition:

```text
For every cell (T,s):
  if CellStatus(T,s) = ALL_SAT,
  then RepairEmpty(T,s) holds.
```

This is not a repair law.
It is a phase-diagram completeness condition.

## 8. UNSAT-Cell Orbit-Fiber Exactness

For `ALL_UNSAT` cells, define:

```text
CellReportKey(T,s,rho)
Fiber(T,s,rho)
RepairOrbit_G(x)
```

where:

```text
rho = q(R)
q_atom(right(voter,P)) = minlib
q_atom(base_atom) = base_atom
G = S2_voters x S4_alternatives
```

Certificate condition:

```text
For every ALL_UNSAT cell (T,s) and every grouped report rho:
  Fiber(T,s,rho) is empty or exactly one complete G-orbit.
```

Also require:

```text
No partial orbit fragments.
Every repair orbit is contained in one cell report fiber.
Orbit-stabilizer equation holds for every repair object:
  |Orb(x)| * |Stab(x)| = 48.
```

## 9. Shape-Blind Support Truncation

Define:

```text
BlindFiber_UNSAT(T,rho)
ShapeSupport_UNSAT(T,rho)
```

where:

```text
ShapeSupport_UNSAT(T,rho)
  := { s | CellStatus(T,s)=ALL_UNSAT and Fiber(T,s,rho) is nonempty }.
```

Certificate condition:

```text
#Orbits(BlindFiber_UNSAT(T,rho))
=
|ShapeSupport_UNSAT(T,rho)|
```

for all `(T,rho)`.

Current audited result:

```text
shape-blind fibers = 33
support truncation law = PASS
```

## 10. Complete Phase-Diagram Certificate

Certificate 2 should certify all 48 cells:

```text
For every cell (T,s):

Case 1: ALL_UNSAT
  repair objects exist;
  cell orbit-fiber exactness holds;
  support truncation law contributes through ShapeSupport_UNSAT.

Case 2: ALL_SAT
  RepairEmpty(T,s) holds.

Case 3: MIXED_WITHIN_SHAPE
  certificate fails or becomes conditional.

Case 4: UNKNOWN
  certificate fails.
```

This closes the full phase-diagram certificate:

```text
UNSAT cells: repair geometry law applies.
SAT cells: repair object universe is empty.
```

## 11. Non-Circularity Conditions

Certificate 2 must verify or record:

```text
T is bundled mask/schema.
Shape is computed from W.
Cell(T,s) is an analysis stratum.
ResidualClass is not defined by collapse behavior.
SAT cells are empty because their fixed-witness theories are SAT, not because
  they would violate the theorem.
UNSAT cells are included because their fixed-witness theories are UNSAT, not
  because the law holds there.
```

## 12. Theorem Candidate Supported by Certificate 2

Candidate:

```text
Mask-Shape Collapse Law.

For every bundled residual mask T and obstruction shape s:

If CellStatus(T,s)=ALL_UNSAT, then:
  every cell-indexed grouped-report fiber is exactly one repair orbit;
  every shape-blind report satisfies
    #Orbits(BlindFiber_UNSAT(T,rho))
    =
    |ShapeSupport_UNSAT(T,rho)|.

If CellStatus(T,s)=ALL_SAT, then:
  RepairEmpty(T,s).
```

This is a candidate theorem supported by finite audit data. It is not a
theorem already proved in Lean.

## 13. Sen24 Internal Resolution Interpretation

Sen's liberal paradox establishes an impossibility boundary.
This phase-diagram certificate resolves the internal structure of that
boundary in Sen24:

```text
which bundled residual masks and obstruction shapes yield inconsistency;
which cells are satisfiable and therefore repair-empty;
and, for every inconsistent cell, how grouped repair reports collapse repair
orbits.
```

This is not a new general Sen theorem.
It is a complete computational internal resolution of the Sen24 bundled-mask x
obstruction-shape phase diagram, under the declared selector-free semantic
encoding and audit assumptions.

## 14. Non-Claims

This design does not claim:

- Lean theorem;
- Certificate 2 implementation;
- checker implementation;
- paper-ready theorem;
- general Sen theorem;
- Arrow theorem;
- Gibbard-Satterthwaite theorem;
- 3-voter theorem;
- family-scale theorem;
- warrant-contract semantics;
- semantic-to-CNF correctness theorem;
- that shape is part of ambient theory identity;
- that SAT cells have repair objects;
- that ResidualClass is defined by the collapse law.

## 15. Expected Checker Outputs

Expected future outputs:

```text
m4_certificate2_cell_statuses.json
m4_certificate2_repair_empty_cells.json
m4_certificate2_unsat_cell_repair_objects.json
m4_certificate2_cell_report_fibers.json
m4_certificate2_repair_orbits.json
m4_certificate2_shape_blind_support.json
m4_certificate2_summary.json
```

Future checker summary fields:

```text
total_cells
all_unsat_cells
all_sat_cells
mixed_within_shape_cells
unknown_cells
repair_empty_cell_count
repair_object_count
repair_orbit_count
cell_report_fiber_count
shape_blind_fiber_count
orbit_fiber_exactness_verdict
repair_empty_verdict
support_truncation_verdict
non_circularity_verdict
certificate2_verdict
```

## 16. Done Conditions

Certificate 2 is done only when a future checker verifies:

- all 48 minlib-active mask-shape cells are covered;
- `ALL_UNSAT = 18`, `ALL_SAT = 30`, `MIXED_WITHIN_SHAPE = 0`, and
  `UNKNOWN = 0`, or the certificate explicitly reports any future deviation;
- every `ALL_UNSAT` cell satisfies orbit-fiber exactness;
- every `ALL_SAT` cell satisfies `RepairEmpty(T,s)`;
- every shape-blind report over UNSAT support satisfies support truncation;
- no repair objects are created for SAT witness instances;
- `T` remains bundled mask/schema identity;
- `(T,s)` remains an analysis cell, not an ambient residual theory.

## 17. Next Authorized Action

The next authorized action is design review of Certificate 2 as a complete
phase-diagram certificate.

No checker implementation, solver rerun, Lean theorem work, 3-voter work,
warrant-contract implementation, or paper-claim promotion is authorized by
this document.
