# M4 Design: Obstruction-Indexed Repair-Orbit Classification

Status: design-only

Depends on: M4 Phase 1 Semantic MUS/MCS Gate, M4 Phase 2
Repair-Orbit/Report-Fiber Precheck, Phase 2 Shape-Blind Diagnostic, and
Report-Shape Support Collapse Diagnostic

Current authorization: theorem-design document only

Not authorized: Lean implementation, 3-voter run, warrant-contract
implementation, paper-claim promotion

## 1. Motivation

M2 classified Sen obstruction shapes O2/O3/O4. Phase 1 showed that O2/O3/O4
shape controls selector-free semantic MUS/MCS geometry. Phase 2 showed that,
once `target_case` and obstruction shape are included in the report context,
each grouped-report fiber is exactly one repair orbit under `S2 x S4`.

The shape-blind diagnostic showed that if shape is removed from the report
context, 16 repair orbits collapse into only 9 grouped-report fibers, and 5 of
those fibers contain multiple orbits. The report-shape support diagnostic
showed that the number of collapsed orbits in a shape-blind fiber equals the
number of obstruction shapes on which that report has support.

Therefore the next candidate M4 theorem should be an obstruction-indexed
orbit-classification theorem. The obstruction-shape index is not decorative; it
is necessary information for orbit-level identifiability in this finite
precheck.

## 2. Core Objects

The candidate theorem language should be built from the following finite
objects.

```text
TargetCase := {case_11101, case_11111}

Witness W := ((voter0,P),(voter1,Q))
where P,Q are unordered pairs of alternatives over {0,1,2,3}

Shape(W) := O2 if P=Q
            O3 if |P intersection Q| = 1
            O4 if P intersection Q = empty

SemanticRepair R := semantic MCS for the selector-free fixed-witness theory of W

RepairObject x := (target_case, W, R)

G := S2_voters x S4_alternatives

q_atom(asymm) = asymm
q_atom(un) = un
q_atom(no_cycle3) = no_cycle3
q_atom(no_cycle4) = no_cycle4
q_atom(right(voter,P)) = minlib

q(R) := { q_atom(a) | a in R }

IndexedReport(x) := (target_case, Shape(W), q(R))

ShapeBlindReport(x) := (target_case, q(R))

Fiber(t,s,rho) := { x | target_case(x)=t, Shape(W_x)=s, q(R_x)=rho }

BlindFiber(t,rho) := { x | target_case(x)=t, q(R_x)=rho }

ShapeSupport(t,rho) := { s in {O2,O3,O4} | Fiber(t,s,rho) is nonempty }
```

The term `minlib` here is a grouped report label for rights-atom deletions, not
a primitive semantic atom.

## 3. Candidate Theorem Statements

These are precheck-supported theorem candidates, not Lean theorems.

### Candidate Theorem A: Obstruction-Indexed Orbit-Fiber Exactness

```text
For every target_case t, obstruction shape s in {O2,O3,O4}, and grouped
report rho, the fiber Fiber(t,s,rho) is either empty or exactly one orbit of G
acting on RepairObject.

Equivalently, for every repair object x,
Fiber(IndexedReport(x)) = Orb_G(x).
```

This is the core exactness statement. It is explicitly obstruction-indexed:
`target_case`, `Shape(W)`, and `q(R)` are all part of the report context.

### Candidate Theorem B: Shape-Blind Collapse

```text
For the same finite two-voter Sen24 semantic repair universe, there exist
target_case t and grouped report rho such that BlindFiber(t,rho) contains more
than one G-orbit.

In the Phase 2 diagnostic:
  number of nonempty indexed fibers = 16
  number of repair orbits = 16
  number of nonempty shape-blind fibers = 9
  number of multi-orbit shape-blind fibers = 5
```

This statement blocks a shape-blind interpretation of grouped reportability.
Grouped report alone does not provide orbit-level identifiability in this
finite precheck.

### Candidate Theorem C: Report-Shape Support Collapse Law

```text
For each target_case t and shape-blind grouped report rho, the number of
repair orbits contained in BlindFiber(t,rho) equals the number of obstruction
shapes on which rho has nonempty indexed support:

#Orbits(BlindFiber(t,rho))
=
|ShapeSupport(t,rho)|.

Observed hierarchy in the finite precheck:
  asymm: O2-only, no collapse
  un: O3/O4 support, intermediate collapse
  minlib: O2/O3/O4 support, maximal Sen24 two-voter shape collapse
  no_cycle4: O3/O4 support in case_11101, O4-only in case_11111
  {no_cycle3,no_cycle4}: O3-only in case_11111, no collapse
```

The phrase "atom-dependent hierarchy" should be read as a report-label /
grouped-repair hierarchy, because `minlib` is a grouped report label for
rights-atom deletions.

## 4. What Makes Theorem C Nontrivial

The content of Theorem C is not the equality alone. The equality is explained
by obstruction-indexed orbit-fiber exactness plus the report's
obstruction-shape support pattern.

The substantive structure is the nonuniform support pattern:

- `minlib` spans all three shapes and produces maximal collapse.
- `asymm` is O2-only and produces no collapse.
- `un` and `no_cycle4` produce intermediate collapse where they span O3/O4.
- The composite report `{no_cycle3,no_cycle4}` is O3-only and follows the same
  support law.

This design does not claim this is a general law of social choice. It does not
claim 3-voter behavior, Arrow or Gibbard-Satterthwaite analogues, an existing
Lean theorem, or a paper-ready theorem.

## 5. Relationship to M2

M2 supplied the obstruction-shape taxonomy O2/O3/O4. Phase 1 showed that this
taxonomy governs MUS/MCS support geometry. Phase 2 and the
shape-blind/support diagnostics show that the same taxonomy is required for
orbit-level identifiability and quantitatively controls shape-blind collapse.

Thus O2/O3/O4 are not merely explanatory labels; they carry the information
needed to prevent grouped-report fibers from collapsing distinct repair
orbits.

## 6. Relationship to M3

M3 established conditions under which grouped repair reporting is
contract-relative and correct. Phase 2 refines the meaning of grouped
reportability in the Sen24 fixed-witness semantic setting: the grouped
`minlib` report is orbit-identifying only when the obstruction-shape index is
part of the contract.

M4 should not replace M3. It refines grouped reportability by identifying the
residual ambiguity as a group orbit and by showing that obstruction shape is
necessary to avoid orbit collapse.

## 7. Relationship to M1.5

M1.5 showed that raw repair reporting is representation-sensitive and
non-canonical. The M4 design candidate does not erase that non-canonicity.
Instead, it asks how much of the ambiguity can be quotiented by an explicit
group action and how much obstruction-shape information is required to recover
orbit-level identifiability.

In the finite Sen24 two-voter semantic repair universe, shape-blind grouped
reports collapse repair orbits in a way controlled by obstruction-shape
support. This does not fully measure all raw-repair non-canonicity.

## 8. Relationship to Warrant

Warrant semantics is not part of this theorem. The orbit-classification result
can later constrain warrant design: if a shape-blind report collapses multiple
repair orbits, then it cannot by itself warrant a unique point repair or a
unique institutional action.

A later warrant layer may define action envelopes over orbit-level reports and
may require authority configuration for point selection among collapsed
orbits. But this design document does not define action semantics, authority,
delegation, or warrant preservation.

## 9. Non-Claims

This design does not claim:

- Lean theorem;
- semantic-to-CNF correctness theorem;
- 3-voter theorem;
- Arrow theorem;
- Gibbard-Satterthwaite theorem;
- general social-choice theorem;
- warrant-contract semantics;
- Delegated Warrant Preservation;
- paper-ready theorem.

## 10. Open Questions Before Implementation

1. Should Theorem A be stated only for the two target residuals, or for all
   selector-free fixed-witness Sen24 residuals satisfying the same semantic
   pattern?
2. Should `target_case` be part of the report index, or should `target_case`
   be treated as an ambient theory parameter?
3. Should `Shape(W)` be part of the report, or part of the surrounding
   obstruction contract?
4. Should `G` be full `S2 x S4`, or a subgroup preserving additional semantic
   structure?
5. What is the minimal finite data needed for a Lean/checker theorem:
   enumerated objects, generated certificates, or a hand-coded finite proof?
6. Should Shape-Blind Collapse be formalized as a theorem, a proposition, or a
   diagnostic lemma?
7. Should Report-Shape Support Collapse Law be formalized as a theorem, a
   proposition, or a diagnostic lemma?
8. How should this theorem feed into a later action-envelope/warrant layer
   without smuggling in authority assumptions?

## 11. Next Authorized Action After This Design

After this design document is reviewed, the next authorized action is a design
review deciding whether to:

```text
(A) implement a finite Lean/checker theorem for the two-voter Sen24
    obstruction-indexed orbit-fiber exactness, shape-blind collapse, and
    report-shape support collapse results;
(B) first design a 3-voter S3 extension precheck;
(C) stop the orbit track and return to warrant-contract design.
```

No implementation choice is authorized by this design document alone.
