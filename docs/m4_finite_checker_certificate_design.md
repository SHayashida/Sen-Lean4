# M4 Design: Finite Checker and Data Certificate for Ambient Repair-Orbit Classification

Status: design-only

Depends on: M4 obstruction-indexed repair-orbit classification design

Current authorization: checker/certificate design only

Not authorized: checker implementation, Lean implementation, solver rerun,
3-voter run, warrant-contract implementation, paper-claim promotion

## 1. Motivation

The Phase 2 result is finite and enumeration-dependent. Before implementing a
Lean theorem, the project needs a finite checker/certificate design that
separates:

1. Coverage of the ambient residual class.
2. Orbit-fiber exactness within each ambient residual theory.
3. Shape-blind collapse and support-collapse law.

This avoids proving a theorem that is either over-indexed or based on only two
unqualified observations.

## 2. Certificate 1: Bundled-Mask Coverage and Cell Status Phase Diagram

Goal:

Verify that the ambient residual theories covered by the theorem are exactly
the intended finite Sen24 two-voter selector-free fixed-witness residual
class, and compute the cell status phase diagram for minlib-active masks.

Inputs:

- list of candidate residual theories `T`;
- residual identifiers, for example `case_11101` and `case_11111`;
- evidence that no other residual theory in the declared finite class is
  UNSAT/relevant;
- provenance connecting this class to earlier residual enumeration artifacts,
  if applicable.

The checker/certificate pipeline must verify that:

- full 64 split universe is treated as an upstream representation artifact;
- bundled-minlib-aligned `ResidualClass` is the M4 ambient theorem scope;
- one-sided split rows are not ambient M4 theories unless an explicit
  theorem-scope decision says otherwise;
- their exclusion is derived from bundled `minlib` schema mapping, not from
  Theorem C.

Required checker outputs:

- `residual_mask_vocabulary`;
- `full_split_universe_vocabulary`;
- `bundled_universe_vocabulary`;
- `block_aligned_sublattice_definition`;
- `block_alignment_provenance_status`;
- `covered_residual_count`;
- `covered_residual_ids`;
- `excluded_residual_count`;
- exclusion criterion;
- whether earlier 64-residual enumeration is sufficient for this semantic
  universe;
- if not sufficient, a required semantic-level residual enumeration task;
- `witness_is_internal_parameter`: true/false;
- `mask_to_named_case_mapping`;
- `minlib_schema_level`: `T`-level or `W`-level;
- `semantic_instantiation_bridge_status`;
- `circularity_check_passed`;
- `full_split_universe_is_upstream_artifact`: true/false;
- `one_sided_split_rows_present`: true/false;
- `one_sided_rows_are_m4_ambient_theories`: true/false;
- `one_sided_rows_m4_scope_status`;
- `one_sided_exclusion_basis`;
- `bundled_minlib_schema_requires_two_person_witness`: true/false;
- `finite_auditability_verdict`.

See `docs/m4_residual_class_coverage_certificate_result.md` for the
Certificate 1 coverage result over the bundled-minlib-aligned
`ResidualClass`. The current result is `CONDITIONAL_PASS`, not `PASS`, because
the full 32-mask semantic enumeration contains `MIXED` masks.

Do not assume that raw/lever residual coverage automatically certifies
selector-free fixed-witness semantic residual coverage. The checker design
must either reuse the earlier coverage artifact with an explicit bridge, or
require a fresh semantic coverage certificate.

The checker must first validate the individuation discipline:

- `T` is a residual lever/axiom mask.
- `W` is not part of `T`.
- `W` ranges internally inside `T`.
- `Shape(W)`, `q(R)`, and `ShapeSupport_T(rho)` are computed outputs, not
  class-defining predicates.

Failure modes:

- `W` is treated as part of residual identity.
- `ResidualClass` is defined by report/shape/orbit behavior.
- Earlier residual enumeration uses a different mask vocabulary with no
  bridge.
- `minlib` is inconsistently treated as a `T`-level schema in one artifact and
  as `W`-level identity in another.
- Treating the full 64 split universe as identical to M4 `ResidualClass`.
- Excluding one-sided split rows because Theorem C would fail.
- Failing to distinguish bundled-minlib-aligned sublattice from full split
  universe.
- Treating `decisive_voter0`-only or `decisive_voter1`-only rows as ambient M4
  theories without an explicit theorem-scope decision.

## 3. Certificate 1b: Mask-Shape Collapse Law Audit Over UNSAT Cells

Certificate 1b is the finite audit recorded in
`docs/m4_mask_shape_collapse_law_audit_result.md`.

Goal:

Verify that repair geometry over `MIXED` residuals is support-truncated rather
than irregular, by checking every UNSAT analysis cell:

```text
Cell(T,s) := { W inside T | Shape(W)=s }
```

The certificate must preserve:

- `T` is bundled residual mask/schema identity;
- `s` is an analysis coordinate, not part of `T`;
- repair objects are built only for UNSAT witness instances in `ALL_UNSAT`
  cells;
- SAT cells contribute no repair objects;
- `ResidualClass` is not defined by the collapse law.

Certificate 1b checks:

- cell statuses `ALL_UNSAT`, `ALL_SAT`, `MIXED_WITHIN_SHAPE`, `UNKNOWN`;
- repair object scope;
- group action well-definedness;
- `q`-invariance;
- cell-indexed orbit-fiber exactness;
- absence of partial orbit fragments;
- orbit-stabilizer;
- shape-blind support truncation law.

The current audit result is `PASS`:

```text
UNSAT cells = 18
UNSAT witness instances = 216
repair objects = 816
repair orbits = 46
cell report fibers = 46
shape-blind fibers = 33
```

Certificate 1b does not complete Certificate 2 and does not promote a Lean
theorem.

## 4. Certificate 2: Complete Cell Phase-Diagram Certificate

If Certificate 1b passes, Certificate 2 should be formalized over the complete
mask-shape phase diagram rather than only ALL_W_UNSAT masks or only UNSAT
repair-object cells. It should certify UNSAT cells by orbit-fiber exactness and
SAT cells as repair-empty.

The certificate domain is the complete cell phase diagram, not only the
nonempty repair-object universe:

```text
16 minlib-active bundled masks x 3 obstruction shapes = 48 cells.
```

Certificate 2 must include both:

1. UNSAT-cell orbit-fiber exactness.
2. SAT-cell repair-empty verification.

For each UNSAT cell `(T,s)` with `Cell(T,s)` equal to `ALL_UNSAT`, verify:

- repair object universe `RepairObject_T`;
- group `G = S2 x S4`;
- group size `48`;
- well-defined group action on `RepairObject_T`;
- `q`-invariance;
- indexed fibers `Fiber_T(s,rho)`;
- repair orbits;
- every nonempty `Fiber_T(s,rho)` is exactly one complete orbit;
- no partial orbit fragments;
- orbit-stabilizer equation holds for every repair object.

For each SAT cell `(T,s)` with `Cell(T,s)` equal to `ALL_SAT`, verify:

- `RepairEmpty(T,s)`;
- no repair object is created for any witness in the cell;
- the cell is empty because its fixed-witness theories are SAT, not because it
  would violate orbit-fiber exactness.

For any `MIXED_WITHIN_SHAPE` or `UNKNOWN` cell, Certificate 2 must fail or
become conditional according to the registered checker policy.

This certificate is the finite-data counterpart of the phase-diagram theorem
candidate: UNSAT cells carry Candidate Theorem A-style orbit-fiber exactness,
and SAT cells carry repair-empty completeness.

It must not redefine `T` as `(T,s)`. The cell coordinate remains an analysis
stratum inside the bundled mask/schema.

## 5. Absorbed Certificate 3/4 Obligations

Old Certificate 3/4 obligations are absorbed into Certificate 2.
They remain as named subchecks but are no longer independent downstream
certificate stages.

Old Certificate 3, Shape-Blind Collapse, becomes the Certificate 2 subcheck
over UNSAT support:

```text
BlindFiber_UNSAT(T,rho)
shape_blind_fiber_count
blind_orbit_count
shape_support_count
support_truncation_law_holds
```

Old Certificate 4, Report-Shape Support Collapse Law, becomes the Certificate
2 support-truncation subcheck:

```text
#Orbits_T(BlindFiber_UNSAT_T(rho))
=
|ShapeSupport_UNSAT_T(rho)|.
```

The checker should still distinguish:

- no collapse;
- intermediate collapse;
- maximal Sen24 two-voter shape collapse.

The support pattern remains a separate certified datum. The checker should not
treat the support law as pure orbit-stabilizer arithmetic.

## 6. Consolidated Certificate Dependency Graph

```text
Certificate 1:
  bundled-mask coverage and cell-status phase diagram

Certificate 1b:
  exploratory mask-shape collapse audit

Certificate 2:
  complete phase-diagram certificate
    - SAT-cell RepairEmpty
    - UNSAT-cell orbit-fiber exactness
    - orbit-stabilizer
    - shape-blind support truncation
    - non-circularity
```

There is no independent Certificate 3 or Certificate 4 implementation stage
after this consolidation unless a later scope decision reintroduces them for a
different purpose.

## 7. Output Artifacts

A future checker should emit the following artifacts:

```text
m4_residual_class_coverage.json
m4_certificate2_cell_statuses.json
m4_certificate2_repair_empty_cells.json
m4_repair_objects.json
m4_group_action.json
m4_indexed_fibers.json
m4_repair_orbits.json
m4_shape_blind_fibers.json
m4_support_collapse.json
m4_checker_summary.json
```

These artifacts are not created by this design document. This is design-only.

## 8. Non-Claims

This checker design does not claim:

- checker implementation exists;
- Lean theorem exists;
- semantic coverage has already been certified unless explicitly bridged;
- 3-voter result;
- Arrow result;
- Gibbard-Satterthwaite result;
- general social-choice theorem;
- warrant-contract semantics;
- paper-ready theorem.

## 9. Next Authorized Action

After this checker/certificate design is reviewed, the next authorized action
is one of:

```text
(A) implement the finite checker/certificate pipeline for the ambient
    two-voter Sen24 theorem candidates;
(B) first resolve the ResidualClass coverage bridge between earlier residual
    enumeration and the selector-free fixed-witness semantic universe;
(C) stop before implementation and revise the theorem scope.
```

No implementation action is authorized by this design document alone.
