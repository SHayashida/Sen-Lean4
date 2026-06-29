# M4 Certificate 2 Result: Complete Phase-Diagram Checker

Status: certificate-result / exploratory finite-data checker

Depends on: Certificate 1 bundled-mask coverage, Mask-Shape Collapse Law
audit, and Certificate 2 phase-diagram design

Current authorization: Certificate 2 checker result only

Not authorized: Lean theorem, solver rerun, 3-voter run,
warrant-contract implementation, paper-claim promotion

## 1. Purpose

This document records the result of the M4 Certificate 2 phase-diagram
checker.

The checker verifies the complete 48-cell minlib-active bundled-mask x
obstruction-shape phase diagram:

```text
16 minlib-active bundled masks x 3 obstruction shapes = 48 cells
```

It verifies both sides of the phase diagram:

- SAT cells are actively repair-empty.
- UNSAT cells satisfy repair-orbit exactness, orbit-stabilizer, and
  shape-blind support truncation.

The checker is a verifier over existing local artifacts. It does not rerun a
solver, Certificate 1, the mask-shape audit, or Lean.

## 2. Inputs

Certificate 1 inputs:

```text
/tmp/sen_m4_residual_class_coverage_certificate/mask_statuses.csv
/tmp/sen_m4_residual_class_coverage_certificate/witness_statuses.csv
/tmp/sen_m4_residual_class_coverage_certificate/residual_class_coverage_certificate.json
/tmp/sen_m4_residual_class_coverage_certificate/boundary_formula.json
```

Mask-shape audit inputs:

```text
/tmp/sen_m4_mask_shape_collapse_law_audit/cell_statuses.csv
/tmp/sen_m4_mask_shape_collapse_law_audit/repair_objects.csv
/tmp/sen_m4_mask_shape_collapse_law_audit/cell_report_fibers.csv
/tmp/sen_m4_mask_shape_collapse_law_audit/repair_orbits.csv
/tmp/sen_m4_mask_shape_collapse_law_audit/shape_blind_fibers.csv
/tmp/sen_m4_mask_shape_collapse_law_audit/support_truncation.csv
/tmp/sen_m4_mask_shape_collapse_law_audit/mask_shape_collapse_certificate.json
```

Checker outputs:

```text
/tmp/sen_m4_certificate2_phase_diagram_checker/m4_certificate2_cell_statuses.json
/tmp/sen_m4_certificate2_phase_diagram_checker/m4_certificate2_repair_empty_cells.json
/tmp/sen_m4_certificate2_phase_diagram_checker/m4_certificate2_unsat_cell_repair_objects.json
/tmp/sen_m4_certificate2_phase_diagram_checker/m4_certificate2_cell_report_fibers.json
/tmp/sen_m4_certificate2_phase_diagram_checker/m4_certificate2_repair_orbits.json
/tmp/sen_m4_certificate2_phase_diagram_checker/m4_certificate2_shape_blind_support.json
/tmp/sen_m4_certificate2_phase_diagram_checker/m4_certificate2_summary.json
/tmp/sen_m4_certificate2_phase_diagram_checker/m4_certificate2_certificate.json
```

## 3. Phase Diagram Coverage

Coverage verdict: `PASS`.

| quantity | value |
| --- | ---: |
| total cells | 48 |
| `ALL_UNSAT` cells | 18 |
| `ALL_SAT` cells | 30 |
| `MIXED_WITHIN_SHAPE` cells | 0 |
| `UNKNOWN` cells | 0 |

The checker also verified:

- 16 minlib-active bundled masks;
- shape membership `O2`, `O3`, `O4` for each minlib-active mask;
- one row for each `(case_id, shape)` cell;
- expected witness counts `O2 = 6`, `O3 = 24`, and `O4 = 6`.

## 4. SAT-Cell RepairEmpty

RepairEmpty verdict: `PASS`.

The checker actively verified all 30 `ALL_SAT` cells. For every SAT cell
`(T,s)`, it checked:

- every witness row in `Cell(T,s)` has status `SAT`;
- no repair object row has `case_id = T` and `shape = s`;
- the repair-object constructor policy is guarded by UNSAT status;
- the empty deletion is not treated as a repair object.

Summary:

| quantity | value |
| --- | ---: |
| repair-empty cells | 30 |
| SAT-cell repair objects | 0 |
| SAT-cell active verification failures | 0 |

## 5. UNSAT-Cell Orbit-Fiber Exactness

UNSAT-cell exactness verdict: `PASS`.

For the 18 `ALL_UNSAT` cells, the checker verified:

- every witness row in the cell has status `UNSAT`;
- repair objects exist only in `ALL_UNSAT` cells;
- every repair object has a matching `ALL_UNSAT` cell;
- every cell-indexed grouped-report fiber is exactly one complete repair
  orbit;
- no cell report fiber contains partial orbit fragments;
- every repair orbit is contained in one cell report fiber.

Counts:

| quantity | value |
| --- | ---: |
| repair objects | 816 |
| repair orbits | 46 |
| cell report fibers | 46 |

## 6. Shape-Blind Support Truncation

Support truncation verdict: `PASS`.

The old Certificate 3/4 obligations are checked as internal Certificate 2
subchecks. For every shape-blind report row, the checker verified:

```text
#Orbits(BlindFiber_UNSAT(T,rho))
=
|ShapeSupport_UNSAT(T,rho)|
```

It also verified that shape support contains only `ALL_UNSAT` cells and that
no SAT cell contributes to `ShapeSupport_UNSAT`.

| quantity | value |
| --- | ---: |
| shape-blind fibers | 33 |
| support truncation failures | 0 |

## 7. Absorbed Certificate 3/4 Obligations

Absorption verdict: `PASS`.

The checker records:

```text
certificate3_independent_stage = false
certificate4_independent_stage = false
certificate3_absorbed_as = shape_blind_support_reporting
certificate4_absorbed_as = support_truncation_subcheck
```

Certificate 3 and Certificate 4 were not implemented as separate stages.
Their obligations are internal Certificate 2 subchecks.

## 8. Non-Circularity

Non-circularity verdict: `PASS`.

The checker recorded and verified:

```text
t_is_bundled_mask_schema = true
shape_computed_from_w = true
cell_is_analysis_stratum = true
residual_class_not_defined_by_collapse_behavior = true
sat_cells_empty_because_sat = true
unsat_cells_included_because_unsat = true
repair_objects_guarded_by_unsat = true
```

Thus `T` remains bundled mask/schema identity, and `(T,s)` remains an
analysis cell rather than an ambient residual theory.

## 9. Verdict

Certificate 2 verdict: `PASS`.

Reason:

```text
all Certificate 2 phase-diagram checks passed
```

Hard checks:

| check | verdict |
| --- | --- |
| phase diagram coverage | `PASS` |
| SAT-cell RepairEmpty | `PASS` |
| UNSAT-cell exactness scope | `PASS` |
| orbit-fiber exactness | `PASS` |
| support truncation | `PASS` |
| Certificate 3/4 absorption | `PASS` |
| non-circularity | `PASS` |

## 10. Interpretation

Certificate 2 closes the finite-data side of the M4 mask-shape phase diagram.

It verifies:

- SAT cells are repair-empty;
- UNSAT cells satisfy orbit-fiber exactness;
- shape-blind support truncation holds over UNSAT support;
- the analysis remains non-circular.

This is a finite-data certificate over the declared Sen24 selector-free
semantic encoding.
It is not a Lean theorem and not a general Sen theorem.

The result supports the path of treating M4 as a complete machine-audited
internal resolution of the Sen24 bundled-mask x obstruction-shape phase
diagram.

A structural explanation of why the collapse law holds, semantic encoding
correctness, and Lean formalization remain separate later phases.

## 11. Non-Claims

This result does not claim:

- Lean theorem;
- paper-ready theorem;
- general Sen theorem;
- Arrow theorem;
- Gibbard-Satterthwaite theorem;
- 3-voter theorem;
- family-scale theorem;
- warrant-contract semantics;
- semantic-to-CNF correctness theorem;
- structural necessity of the Mask-Shape Collapse Law;
- correctness of the semantic encoding beyond the declared audit assumptions.

## 12. Next Authorized Action

The next authorized action is review of the Certificate 2 checker result and
its output artifacts.

No Lean theorem, solver rerun, 3-voter work, warrant-contract implementation,
paper-claim promotion, or production-encoding change is authorized by this
result document.
