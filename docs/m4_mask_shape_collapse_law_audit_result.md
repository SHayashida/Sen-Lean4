# M4 Audit Result: Mask-Shape Collapse Law

Status: exploratory audit result

Depends on: M4 Certificate 1 ResidualClass coverage output

Current authorization: mask-shape phase-diagram audit only

Not authorized: Lean theorem, Certificate 2 completion, 3-voter run,
warrant-contract implementation, paper-claim promotion

## 1. Purpose

This audit checks whether `MIXED` bundled residual masks are repair-geometry
failures or support-truncated cases.

The result supports the support-truncation interpretation:

```text
MIXED residuals are not repair-geometry failures.
They are coverage/support truncations:
  some obstruction shapes are SAT and drop out;
  every remaining UNSAT (mask, shape) cell satisfies the same repair-orbit /
  collapse law.
```

## 2. Input Certificate

The audit consumed the existing Certificate 1 output artifacts:

```text
/tmp/sen_m4_residual_class_coverage_certificate/mask_statuses.csv
/tmp/sen_m4_residual_class_coverage_certificate/witness_statuses.csv
/tmp/sen_m4_residual_class_coverage_certificate/residual_class_coverage_certificate.json
/tmp/sen_m4_residual_class_coverage_certificate/boundary_formula.json
```

It did not rerun Certificate 1.

Audit outputs were written to:

```text
/tmp/sen_m4_mask_shape_collapse_law_audit/cell_statuses.csv
/tmp/sen_m4_mask_shape_collapse_law_audit/repair_objects.csv
/tmp/sen_m4_mask_shape_collapse_law_audit/cell_report_fibers.csv
/tmp/sen_m4_mask_shape_collapse_law_audit/repair_orbits.csv
/tmp/sen_m4_mask_shape_collapse_law_audit/shape_blind_fibers.csv
/tmp/sen_m4_mask_shape_collapse_law_audit/support_truncation.csv
/tmp/sen_m4_mask_shape_collapse_law_audit/mask_shape_collapse_summary.json
/tmp/sen_m4_mask_shape_collapse_law_audit/mask_shape_collapse_certificate.json
```

## 3. Analysis Unit and Non-Circularity

The ambient residual theory T remains individuated by bundled residual
mask/schema.
Shape is not part of T identity.
Shape(W) is computed from the internal witness configuration W.
The pair (T, Shape(W)) is an analysis cell, not a new ambient theory.

This preserves the option (a) discipline from the coverage bridge:

```text
T is not (mask,W);
T is not (mask,shape);
ResidualClass is not defined by the collapse law.
```

The audit defines:

```text
Cell(T,s) := { W inside T | Shape(W)=s }.
UNSATCell(T,s) holds when every W in Cell(T,s) is UNSAT.
Repair objects are defined only for UNSAT witness instances in those cells.
```

Non-circularity verdict: `PASS`.

## 4. Cell Status Phase Diagram

The audit checked all minlib-active bundled masks and all obstruction shapes
`O2`, `O3`, and `O4`. Expected witness counts were verified as:

```text
O2 = 6
O3 = 24
O4 = 6
```

Cell status counts:

| cell_status | count |
| --- | ---: |
| `ALL_UNSAT` | 18 |
| `ALL_SAT` | 30 |
| `MIXED_WITHIN_SHAPE` | 0 |
| `UNKNOWN` | 0 |

Phase diagram:

| case_id | mask status | O2 | O3 | O4 |
| --- | --- | --- | --- | --- |
| `case_00100` | `ALL_W_SAT` | `ALL_SAT` | `ALL_SAT` | `ALL_SAT` |
| `case_00101` | `ALL_W_SAT` | `ALL_SAT` | `ALL_SAT` | `ALL_SAT` |
| `case_00110` | `ALL_W_SAT` | `ALL_SAT` | `ALL_SAT` | `ALL_SAT` |
| `case_00111` | `ALL_W_SAT` | `ALL_SAT` | `ALL_SAT` | `ALL_SAT` |
| `case_01100` | `ALL_W_SAT` | `ALL_SAT` | `ALL_SAT` | `ALL_SAT` |
| `case_01101` | `MIXED` | `ALL_SAT` | `ALL_UNSAT` | `ALL_UNSAT` |
| `case_01110` | `MIXED` | `ALL_SAT` | `ALL_UNSAT` | `ALL_SAT` |
| `case_01111` | `MIXED` | `ALL_SAT` | `ALL_UNSAT` | `ALL_UNSAT` |
| `case_10100` | `MIXED` | `ALL_UNSAT` | `ALL_SAT` | `ALL_SAT` |
| `case_10101` | `MIXED` | `ALL_UNSAT` | `ALL_SAT` | `ALL_SAT` |
| `case_10110` | `MIXED` | `ALL_UNSAT` | `ALL_SAT` | `ALL_SAT` |
| `case_10111` | `MIXED` | `ALL_UNSAT` | `ALL_SAT` | `ALL_SAT` |
| `case_11100` | `MIXED` | `ALL_UNSAT` | `ALL_SAT` | `ALL_SAT` |
| `case_11101` | `ALL_W_UNSAT` | `ALL_UNSAT` | `ALL_UNSAT` | `ALL_UNSAT` |
| `case_11110` | `MIXED` | `ALL_UNSAT` | `ALL_UNSAT` | `ALL_SAT` |
| `case_11111` | `ALL_W_UNSAT` | `ALL_UNSAT` | `ALL_UNSAT` | `ALL_UNSAT` |

The formal repair-geometry target is the 18 `ALL_UNSAT` cells.

## 5. Repair Object Universe

Repair objects were built only for UNSAT witness instances in `ALL_UNSAT`
cells.

| quantity | value |
| --- | ---: |
| UNSAT cells | 18 |
| UNSAT witness instances | 216 |
| repair objects | 816 |
| repair orbits | 46 |
| cell report fibers | 46 |
| shape-blind fibers | 33 |

The MIXED-only scratch diagnostic comparison matched:

| quantity | observed | expected |
| --- | ---: | ---: |
| MIXED-only UNSAT witness rows | 144 | 144 |
| MIXED-only repair objects | 540 | 540 |
| MIXED-only repair orbits | 30 | 30 |
| MIXED-only cell report fibers | 30 | 30 |
| MIXED-only shape-blind fibers | 24 | 24 |

The combined comparison also matched:

| quantity | observed | expected |
| --- | ---: | ---: |
| ALL_W_UNSAT repair objects | 276 | 276 |
| ALL_W_UNSAT repair orbits | 16 | 16 |
| combined repair objects | 816 | 816 |
| combined repair orbits | 46 | 46 |

Repair-object scope verdict: `PASS`.

## 6. Cell Orbit-Fiber Exactness

The audit uses:

```text
G = S2_voters x S4_alternatives
|G| = 48
```

The action fixes the bundled mask `T`, acts on `W`, acts on rights atoms
accordingly, fixes base atoms, and preserves `Shape(W)`.

Verification results:

| check | verdict |
| --- | --- |
| well-defined group action | `PASS` |
| `q`-invariance | `PASS` |
| every cell report fiber is one complete repair orbit | `PASS` |
| no partial orbit fragments | `PASS` |
| every repair orbit is contained in one cell report fiber | `PASS` |
| orbit-stabilizer equation | `PASS` |

Thus every nonempty cell-indexed grouped-report fiber over the 18 UNSAT cells
is exactly one complete repair orbit.

## 7. Shape-Blind Support Truncation Law

For every shape-blind report key `(T, report)`, the audit checked:

```text
blind_orbit_count(T, report) = |ShapeSupport_UNSAT(T, report)|
```

Result: `PASS` for all 33 shape-blind fibers.

Blind-orbit-count distribution:

| blind orbit count | fiber count |
| ---: | ---: |
| 1 | 22 |
| 2 | 9 |
| 3 | 2 |

Shape-support distribution:

| shape support | fiber count |
| --- | ---: |
| `O2` | 13 |
| `O2;O3` | 1 |
| `O2;O3;O4` | 2 |
| `O3` | 7 |
| `O3;O4` | 8 |
| `O4` | 2 |

The full row-level table is recorded in:

```text
/tmp/sen_m4_mask_shape_collapse_law_audit/shape_blind_fibers.csv
/tmp/sen_m4_mask_shape_collapse_law_audit/support_truncation.csv
```

## 8. Relation to Previous ALL_W_UNSAT Theorem C

The earlier ALL_W_UNSAT-scoped collapse law is a special case of the
mask-shape phase diagram:
ALL_W_UNSAT masks have all three shapes as UNSAT cells.
MIXED masks have only some shapes as UNSAT cells.
The repair geometry law holds on every UNSAT cell; SAT cells contribute no
repair objects.

Therefore the previous ALL_W_UNSAT-only reading remains a conservative
interim scope, but it is too narrow for the observed mask-shape phase diagram.

## 9. Interpretation

MIXED does not mean irregular repair geometry.
MIXED means support truncation: some obstruction shapes are SAT and drop out,
while remaining UNSAT shapes obey the same orbit-fiber and support-collapse
law.

The predictor is not Shape(W) alone.
The relevant unit is the pair:

```text
residual mask T plus obstruction shape Shape(W).
```

This does not make `(T, Shape(W))` a new ambient residual theory. It is an
analysis cell internal to `T`.

## 10. Non-Claims

This result does not claim:

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
- that MIXED masks have full-mask repair geometry under the old T-only reading.

## 11. Audit Verdict

Audit verdict: `PASS`.

Reason:

```text
All mask-shape collapse checks passed.
```

Summary:

| check | verdict |
| --- | --- |
| no `UNKNOWN` cells | `PASS` |
| no `MIXED_WITHIN_SHAPE` cells | `PASS` |
| repair objects only for `ALL_UNSAT` cells | `PASS` |
| well-defined group action | `PASS` |
| `q`-invariance | `PASS` |
| cell orbit-fiber exactness | `PASS` |
| orbit-stabilizer | `PASS` |
| support truncation law | `PASS` |
| non-circularity | `PASS` |

## 12. Next Authorized Action

The next authorized action is a design review of the mask-shape phase diagram
scope decision.

If accepted, Certificate 2 should be redesigned as a complete phase-diagram
certificate over analysis cells `(T,s)` while preserving `T` as bundled
mask/schema identity. This audit does not itself complete Certificate 2.

## 13. Follow-up

Certificate 2 design should include SAT-cell repair-empty checks so that the
full 48-cell phase diagram is certified, not only the 18 UNSAT cells.
