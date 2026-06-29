# M4 Design: Obstruction-Indexed Repair-Orbit Classification

Status: design-only

Depends on: M4 Phase 1 Semantic MUS/MCS Gate, M4 Phase 2
Repair-Orbit/Report-Fiber Precheck, Phase 2 Shape-Blind Diagnostic, and
Report-Shape Support Collapse Diagnostic

Current authorization: theorem-design document only

Not authorized: Lean implementation, 3-voter run, solver rerun,
warrant-contract implementation, paper-claim promotion

## 1. Motivation

M2 classified Sen obstruction shapes O2/O3/O4. Phase 1 showed that O2/O3/O4
shape controls selector-free semantic MUS/MCS geometry. Phase 2 showed that,
once obstruction shape is included in the report context inside a fixed
residual theory, each grouped-report fiber is exactly one repair orbit under
`S2 x S4`.

The shape-blind diagnostic showed that if shape is removed from the report
context, 16 repair orbits collapse into only 9 grouped-report fibers, and 5 of
those fibers contain multiple orbits. The report-shape support diagnostic
showed that the number of collapsed orbits in a shape-blind fiber equals the
number of obstruction shapes on which that report has support.

Therefore the next candidate M4 theorem should be an obstruction-indexed
orbit-classification theorem. The obstruction-shape index is not decorative; it
is necessary information for orbit-level identifiability in this finite
precheck.

## 2. Ambient Residual Theory Parameter

The theorem design treats the residual theory as an ambient parameter, not as
part of the grouped report.

```text
Ambient residual theory T in ResidualClass
```

The observed cases `case_11101` and `case_11111` are named ambient residual
theories `T`. They remain valid data and implementation identifiers, but they
are not report-key components.

The ambient theory parameter `T` is not part of the grouped report. It selects
the finite residual theory in which the repair universe, fibers, and orbits
are computed. The report itself is indexed by obstruction shape and grouped
repair label within `T`.

This prevents over-indexing: the theorem is not that
`(target_case, Shape(W), q(R))` identifies an orbit. The intended statement is
that, for each ambient residual theory `T` in the certified finite residual
class, `(Shape(W), q(R))` identifies an orbit inside `RepairObject_T`.

## 3. ResidualClass and Coverage Obligation

Current intended class:

```text
ResidualClass := the finite class of Sen24 two-voter selector-free
fixed-witness UNSAT residual theories relevant to the Phase 2 semantic repair
universe.
```

ResidualClass elements are individuated by residual lever/axiom masks, not by
witness configurations. `W` is internal to `T`. The symbol `T` denotes a
residual schema. It is fixed before `W` ranges over fixed-witness
configurations.

Therefore, `ShapeSupport_T(rho)` is meaningful: it records which obstruction
shapes appear inside a fixed residual schema `T` as `W` varies.

To justify quantifying over `T in ResidualClass`, a finite coverage
certificate is required. The checker must verify that the ambient residual
theories covered by the theorem are exactly the intended finite UNSAT residual
class.

Existing residual-enumeration evidence may already cover the relevant two
UNSAT cases, but the design must distinguish:

1. Coverage at the earlier raw/lever residual level.
2. Coverage of the selector-free fixed-witness semantic residual theories used
   by Phase 2.

If the earlier 64-residual enumeration is not already a certificate for the
Phase 2 semantic universe, the finite checker must include a separate coverage
certificate for the semantic residual class.

Non-circularity discipline: `ResidualClass` is defined by residual
masks/schemas only. It must not be defined by `ShapeSupport_T`, `q`-fibers,
orbit decomposition, or Report-Shape Support Collapse Law.

The finite-universal reading of Theorem A/B/C depends on a coverage bridge
that separates the full split representation universe from the
bundled-minlib-aligned M4 `ResidualClass`. One-sided split rows are upstream
representation artifacts; they are outside M4 scope only by bundled `minlib`
schema definition, never by appeal to Theorem C.

The full 64 split universe is an upstream representation-level artifact and is
not identical to the M4 `ResidualClass`.

The M4 `ResidualClass` is bundled-minlib-aligned:

- `minlib` is a `T`-level schema;
- `W` ranges internally;
- `decisive_voter0`-only and `decisive_voter1`-only split rows are not ambient
  residual theories `T`.

One-sided split rows must not be excluded by appeal to Theorem C. They are
outside M4 `ResidualClass` only if the bundled `minlib` schema definition fails
to instantiate them as valid ambient residual theories.

Thus the observed `case_11101` and `case_11111` diagnostics are instances of
the ambient theorem schema over the currently covered finite residual
theories. They become finite-universal statements only after the checker
validates the `ResidualClass` coverage certificate.

Certificate 1 now has an exploratory result document at
`docs/m4_residual_class_coverage_certificate_result.md`. The result is
`CONDITIONAL_PASS`: `case_11101` and `case_11111` are exactly the
`ALL_W_UNSAT` masks, but the full 32-mask semantic enumeration contains
`MIXED` residual theories, so theorem scope must be resolved before
Certificate 2 or Lean theorem work.

Scope update after the mask-shape audit:
the natural theorem candidate is no longer only an ALL_W_UNSAT mask-level law.
The candidate is a Mask-Shape Collapse Law over UNSAT analysis cells `(T,s)`,
while preserving `T` as mask/schema identity. The cell coordinate is computed
from internal witness geometry; it is not a new ambient residual theory.

Certificate 2 scope update:
the M4 theorem candidate is now best understood as a phase-diagram law.
UNSAT cells carry repair-orbit exactness and support truncation; SAT cells are
repair-empty. The analysis unit is `Cell(T,s)`, but `T` remains a bundled
residual mask/schema.

Pipeline consolidation note:
the theorem candidate is supported by a consolidated finite-data pipeline.
Certificate 1 establishes the cell phase diagram; Certificate 2 certifies
SAT-cell emptiness and UNSAT-cell repair geometry, including the former
Certificate 3/4 support-truncation obligations.

## 4. Core Objects

The candidate theorem language should be built from the following finite
objects.

```text
Ambient residual theory T in ResidualClass

Witness W := ((voter0,P),(voter1,Q))
where P,Q are unordered pairs of alternatives over {0,1,2,3}

Shape(W) := O2 if P=Q
            O3 if |P intersection Q| = 1
            O4 if P intersection Q = empty

SemanticRepair_T R :=
  semantic MCS for the selector-free fixed-witness theory of T at W

RepairObject_T x := (W, R)
where W is a fixed witness configuration and
R is a semantic MCS for the selector-free fixed-witness theory of T at W.

G := S2_voters x S4_alternatives

q_atom(asymm) = asymm
q_atom(un) = un
q_atom(no_cycle3) = no_cycle3
q_atom(no_cycle4) = no_cycle4
q_atom(right(voter,P)) = minlib

q(R) := { q_atom(a) | a in R }

IndexedReport_T(x) := (Shape(W), q(R))

ShapeBlindReport_T(x) := q(R)

Fiber_T(s,rho) :=
  { x in RepairObject_T | Shape(W_x)=s and q(R_x)=rho }

BlindFiber_T(rho) :=
  { x in RepairObject_T | q(R_x)=rho }

ShapeSupport_T(rho) :=
  { s in {O2,O3,O4} | Fiber_T(s,rho) is nonempty }
```

The term `minlib` here is a grouped report label for rights-atom deletions, not
a primitive semantic atom.

## 5. Candidate Theorem Statements

These are precheck-supported theorem candidates, not Lean theorems. They
become finite-universal statements only after the checker validates the
`ResidualClass` coverage certificate.

### Candidate Theorem A: Ambient Obstruction-Indexed Orbit-Fiber Exactness

```text
For every ambient residual theory T in ResidualClass,
for every obstruction shape s in {O2,O3,O4},
and for every grouped report rho,
the fiber Fiber_T(s,rho) is either empty or exactly one orbit of G acting on
RepairObject_T.

Equivalently, for every repair object x in RepairObject_T,

  Fiber_T(IndexedReport_T(x)) = Orb_G^T(x).

Here G = S2_voters x S4_alternatives, acting within the repair universe of T.
```

This is the core exactness statement. It is explicitly obstruction-indexed
inside `T`: `Shape(W)` and `q(R)` are part of the report context, while `T` is
the ambient residual theory parameter.

### Candidate Theorem B: Ambient Shape-Blind Collapse

```text
There exists an ambient residual theory T in ResidualClass
and a grouped report rho such that BlindFiber_T(rho)
contains more than one G-orbit.

In the Phase 2 diagnostic over the currently covered residual theories:
  nonempty indexed fibers = 16
  repair orbits = 16
  nonempty shape-blind fibers = 9
  multi-orbit shape-blind fibers = 5
```

This statement blocks a shape-blind interpretation of grouped reportability.
Grouped report alone does not provide orbit-level identifiability in this
finite precheck.

### Candidate Theorem C: Ambient Report-Shape Support Collapse Law

```text
For every ambient residual theory T in ResidualClass
and every shape-blind grouped report rho,
the number of repair orbits contained in BlindFiber_T(rho)
equals the number of obstruction shapes on which rho has nonempty indexed
support:

#Orbits_T(BlindFiber_T(rho))
=
|ShapeSupport_T(rho)|.
```

The content is not the equality alone. The equality follows from:

1. Ambient obstruction-indexed orbit-fiber exactness.
2. The nonuniform obstruction-shape support pattern of grouped report labels
   within `T`.

Observed hierarchy in the finite precheck:

```text
asymm: O2-only, no collapse
un: O3/O4 support, intermediate collapse
minlib: O2/O3/O4 support, maximal Sen24 two-voter shape collapse
no_cycle4: O3/O4 support in case_11101, O4-only in case_11111
{no_cycle3,no_cycle4}: O3-only in case_11111, no collapse
```

The phrase "atom-dependent hierarchy" should be read as a report-label /
grouped-repair hierarchy, because `minlib` is a grouped report label for
rights-atom deletions.

## 6. Observed Diagnostics as Instances

The observed diagnostics are retained, but reframed as named ambient residual
theory instances rather than report-key entries.

```text
Shape-indexed fibers: 16
Repair orbits: 16
Shape-blind fibers: 9
Multi-orbit shape-blind fibers: 5 / 9
Support-collapse equality:
  blind_orbit_count(rho) = shape_support_count(rho) holds for all 9 reports
```

The observed cases `case_11101` and `case_11111` are treated as named ambient
residual theories `T`. They are not report-key components. The diagnostics are
instances of the ambient theorem schema over the currently covered finite
residual theories.

## 7. What Makes Theorem C Nontrivial

The content of Theorem C is not the equality alone. The equality is explained
by ambient obstruction-indexed orbit-fiber exactness plus the report's
obstruction-shape support pattern within `T`.

The substantive structure is the nonuniform support pattern:

- `minlib` spans all three shapes and produces maximal collapse.
- `asymm` is O2-only and produces no collapse.
- `un` and `no_cycle4` produce intermediate collapse where they span O3/O4.
- The composite report `{no_cycle3,no_cycle4}` is O3-only and follows the same
  support law.

This design does not claim this is a general law of social choice. It does not
claim 3-voter behavior, Arrow or Gibbard-Satterthwaite analogues, an existing
Lean theorem, or a paper-ready theorem.

The observed maximal collapse of `minlib` should be connected to the
two-person structure of Sen liberalism only as a precheck-supported
interpretation. It is not yet a separate theorem that all coverage exclusions
and collapse patterns derive from a single schema-level source.

## 8. Relationship to M2

M2 supplied the obstruction-shape taxonomy O2/O3/O4. Phase 1 showed that this
taxonomy governs MUS/MCS support geometry. Phase 2 and the
shape-blind/support diagnostics show that the same taxonomy is required for
orbit-level identifiability and quantitatively controls shape-blind collapse.

Thus O2/O3/O4 are not merely explanatory labels; they carry the information
needed to prevent grouped-report fibers from collapsing distinct repair
orbits.

## 9. Relationship to M3

M3 established conditions under which grouped repair reporting is
contract-relative and correct. Phase 2 refines the meaning of grouped
reportability in the Sen24 fixed-witness semantic setting: the grouped
`minlib` report is orbit-identifying only when the obstruction-shape index is
part of the contract inside the ambient residual theory `T`.

M4 should not replace M3. It refines grouped reportability by identifying the
residual ambiguity as a group orbit and by showing that obstruction shape is
necessary to avoid orbit collapse.

## 10. Relationship to M1.5

M1.5 showed that raw repair reporting is representation-sensitive and
non-canonical. The M4 design candidate does not erase that non-canonicity.
Instead, it asks how much of the ambiguity can be quotiented by an explicit
group action and how much obstruction-shape information is required to recover
orbit-level identifiability.

In the finite Sen24 two-voter semantic repair universe, shape-blind grouped
reports collapse repair orbits in a way controlled by obstruction-shape
support. This does not fully measure all raw-repair non-canonicity.

## 11. Relationship to Warrant

Warrant semantics is not part of this theorem. The orbit-classification result
can later constrain warrant design: if a shape-blind report collapses multiple
repair orbits, then it cannot by itself warrant a unique point repair or a
unique institutional action.

A later warrant layer may define action envelopes over orbit-level reports and
may require authority configuration for point selection among collapsed
orbits. But this design document does not define action semantics, authority,
delegation, or warrant preservation.

## 12. Non-Claims

This design does not claim:

- Lean theorem;
- semantic-to-CNF correctness theorem;
- ResidualClass coverage has already been certified;
- 3-voter theorem;
- Arrow theorem;
- Gibbard-Satterthwaite theorem;
- general social-choice theorem;
- warrant-contract semantics;
- Delegated Warrant Preservation;
- paper-ready theorem.

## 13. Open Questions Before Implementation

1. Can the earlier 64-residual enumeration be reused as a `ResidualClass`
   coverage certificate for the selector-free fixed-witness semantic universe?
2. If not, what semantic-level residual enumeration is required?
3. Should `T` range over exactly `{case_11101, case_11111}`, or over a larger
   declared residual class whose UNSAT/relevant subset is certified to be those
   two cases?
4. Should the final theorem quantify over `T in ResidualClass`, or state two
   named finite instances plus a shared schema?
5. Should the finite checker, rather than Lean, own the coverage and orbit
   enumeration proof obligations?
6. Has the residual-mask vocabulary in the earlier 64-residual enumeration
   been matched to the Phase 2 residual schema vocabulary?
7. Does any artifact treat `W` as part of `T`, contrary to the intended option
   (a)?
8. What bridge evidence shows that semantic fixed-witness instantiation
   creates internal `W`-instances rather than new ambient residual theories?
9. Should `Shape(W)` be part of the report, or part of the surrounding
   obstruction contract?
10. Should `G` be full `S2 x S4`, or a subgroup preserving additional semantic
   structure?
11. How should this theorem feed into a later action-envelope/warrant layer
   without smuggling in authority assumptions?

## 14. Next Authorized Action After This Design

After this theorem design and the finite checker/certificate design are
reviewed, the next authorized action is a design review deciding whether to:

```text
(A) implement the finite checker/certificate pipeline for the ambient
    two-voter Sen24 theorem candidates;
(B) first resolve the ResidualClass coverage bridge between earlier residual
    enumeration and the selector-free fixed-witness semantic universe;
(C) stop before implementation and revise the theorem scope.
```

No implementation choice is authorized by this design document alone.
