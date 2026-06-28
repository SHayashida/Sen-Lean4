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

## 2. Certificate 1: ResidualClass Coverage

Goal:

Verify that the ambient residual theories covered by the theorem are exactly
the intended finite Sen24 two-voter selector-free fixed-witness UNSAT residual
class.

Inputs:

- list of candidate residual theories `T`;
- residual identifiers, for example `case_11101` and `case_11111`;
- evidence that no other residual theory in the declared finite class is
  UNSAT/relevant;
- provenance connecting this class to earlier residual enumeration artifacts,
  if applicable.

Required checker outputs:

- `covered_residual_count`;
- `covered_residual_ids`;
- `excluded_residual_count`;
- exclusion criterion;
- whether earlier 64-residual enumeration is sufficient for this semantic
  universe;
- if not sufficient, a required semantic-level residual enumeration task.

Do not assume that raw/lever residual coverage automatically certifies
selector-free fixed-witness semantic residual coverage. The checker design
must either reuse the earlier coverage artifact with an explicit bridge, or
require a fresh semantic coverage certificate.

## 3. Certificate 2: Ambient Orbit-Fiber Exactness

For each `T in ResidualClass`, verify:

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

This certificate is the finite-data counterpart of Candidate Theorem A.

## 4. Certificate 3: Shape-Blind Collapse

For each `T in ResidualClass`, verify:

- shape-blind fibers `BlindFiber_T(rho)`;
- number of repair orbits inside each `BlindFiber_T(rho)`;
- whether any `BlindFiber_T(rho)` contains multiple orbits;
- aggregate count of indexed fibers, shape-blind fibers, and repair orbits
  over the covered class.

For the current Phase 2 diagnostic:

```text
indexed fibers = 16
repair orbits = 16
shape-blind fibers = 9
multi-orbit shape-blind fibers = 5
```

This certificate is the finite-data counterpart of Candidate Theorem B.

## 5. Certificate 4: Report-Shape Support Collapse Law

For each `T in ResidualClass` and each shape-blind grouped report `rho`,
verify:

```text
#Orbits_T(BlindFiber_T(rho))
=
|ShapeSupport_T(rho)|.
```

Also report:

- `shape_support_T(rho)`;
- support count;
- blind orbit count;
- `blind_mu`;
- `indexed_mu_by_shape`;
- collapse class.

The checker should distinguish:

- no collapse;
- intermediate collapse;
- maximal Sen24 two-voter shape collapse.

This certificate is the finite-data counterpart of Candidate Theorem C.

## 6. Certificate Dependency Graph

```text
ResidualClass coverage
  -> defines the finite quantification domain T in ResidualClass

Orbit-fiber exactness
  -> makes indexed fibers equal repair orbits

Shape-blind collapse
  -> shows that removing Shape(W) collapses repair orbits

Report-shape support collapse law
  -> derives collapse count from support pattern, using exactness plus support data
```

The checker should not treat Theorem C as pure orbit-stabilizer arithmetic.
The support pattern is a separate certified datum.

## 7. Output Artifacts

A future checker should emit the following artifacts:

```text
m4_residual_class_coverage.json
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
