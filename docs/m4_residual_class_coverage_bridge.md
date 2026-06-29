# M4 Coverage Bridge: ResidualClass Individuation

Status: design/audit-only

Depends on: M4 ambient repair-orbit classification design and finite
checker/certificate design

Current authorization: define ResidualClass individuation and coverage-bridge
obligations

Not authorized: solver rerun, Lean implementation, checker implementation,
3-voter run, warrant-contract implementation, paper-claim promotion

## 1. Core Decision

Decision: adopt option (a).

ResidualClass elements are individuated by residual lever/axiom masks over the
declared Sen24 two-voter residual universe.

A witness configuration `W` is not part of the identity of `T`. `W` is
quantified internally when constructing the selector-free fixed-witness
semantic repair universe for `T`.

Thus:

```text
T := residual schema determined by an active lever/axiom mask.
W := internal fixed-witness parameter of T.
RepairObject_T := (W, R).
```

The residual theory `T` is not merely a set of base atoms such as
`asymm/un/no_cycle3/no_cycle4`. It is the residual schema determined by the
declared active levers/axiom atoms, including whether the liberalism/minlib
schema is active. When the minlib schema is active, Phase 2 instantiates it at
each `W` as selector-free semantic rights atoms
`right(voter0,P), right(voter1,Q)`.

## 2. Rejected Alternatives

### Reject Option (b)

Reject option (b): `T` is not individuated by `(mask, W)`.

If `W` were part of `T`, then `Shape(W)` would be built into the identity of
the ambient theory. `ShapeSupport_T(rho)` would become degenerate or local to
one witness configuration. That would destroy the intended theorem, whose
content is that a fixed ambient residual theory `T` generates different
obstruction-shape support patterns as `W` ranges internally.

### Forbid Option (c)

Forbid option (c): `ResidualClass` must not be defined by shape support,
report existence, orbit-fiber exactness, or the support-collapse law.

`ResidualClass` must be defined before Theorem A/B/C. Otherwise the theorem
would be circular: the class quantified over would be selected using the
property being proved.

Forbidden definitions include:

```text
ResidualClass := theories whose reports have stable shape support
ResidualClass := theories whose q-fibers decompose into orbits
ResidualClass := theories satisfying Report-Shape Support Collapse Law
ResidualClass := theories for which minlib spans O2/O3/O4
```

## 3. Correct Type Discipline

```text
ResidualClass
  = finite set of residual masks/schemas T
    over the declared Sen24 two-voter residual universe.

For each T:
  W ranges over the fixed-witness configurations.
  Shape(W) is computed from W.
  SemanticRepair_T(W) is computed from the selector-free fixed-witness theory of T at W.
  RepairObject_T = { (W,R) | R is a semantic MCS for T at W }.
  IndexedReport_T(W,R) = (Shape(W), q(R)).
  ShapeBlindReport_T(W,R) = q(R).
  ShapeSupport_T(rho) is computed after W ranges internally.
```

`Shape(W)`, `q(R)`, `ShapeSupport_T(rho)`, and orbit-fiber behavior are
outputs of the analysis inside `T`, not inputs to the definition of `T`.

## 4. Coverage Bridge Obligation

The coverage bridge must establish that the finite set of `T` over which
Theorem A/B/C quantify is exactly the intended residual-mask class.

If the earlier 64-residual enumeration is over the same residual lever/axiom
masks, then it is a candidate coverage artifact for `ResidualClass`.

However, it is not automatically sufficient for the Phase 2 selector-free
fixed-witness semantic repair universe.

A bridge must show:

1. The mask vocabulary matches.
2. The active/inactive semantics of each lever matches.
3. The two named theories `case_11101` and `case_11111` correspond to the
   intended masks.
4. Every other mask is excluded by a declared criterion.
5. The semantic fixed-witness instantiation does not introduce additional
   ambient residual theories `T`, but only internal `W`-instances of an
   already fixed `T`.

## 5. Coverage Bridge Scenarios

### Scenario 1: Bridge Succeeds

Earlier 64-residual enumeration and Phase 2 semantic universe share the same
residual-mask vocabulary. `W` is internal to each `T`. The only
UNSAT/relevant masks are `case_11101` and `case_11111`.

Then Theorem A/B/C may be stated over a finite `ResidualClass` whose relevant
UNSAT part is fully covered by those two ambient theories.

### Scenario 2: Semantic Bridge Requires Extra Enumeration

The earlier 64-residual enumeration is not enough to certify the
selector-free fixed-witness semantic universe.

Then a separate semantic-level coverage certificate is required. This may
enumerate residual masks `T` and, inside each `T`, all `W` instances. The
enumeration must not redefine `T` as `(mask,W)`.

### Scenario 3: Circular Definition Detected

`ResidualClass` is found to depend on shape support, report labels,
orbit-fiber exactness, or support-collapse behavior.

Then the definition is invalid and must be rewritten before any checker or
theorem work.

## 6. Immediate Next Audit Questions

1. What is the exact mask/lever vocabulary of the earlier 64-residual
   enumeration?
2. Does that vocabulary match the residual-mask vocabulary used by Phase 2?
3. Do `case_11101` and `case_11111` name masks, not witness configurations?
4. Is `minlib` represented as an active schema at `T`-level and instantiated
   into `right(voter,P)` atoms only after `W` is chosen?
5. Does any Phase 2 output or script accidentally treat `W` as part of
   residual identity?
6. Are `Shape(W)`, `q(R)`, and `ShapeSupport_T(rho)` computed after `T` is
   fixed, rather than used to define `T`?
7. What exclusion criterion certifies that other masks are outside the
   relevant UNSAT/relevant class?
8. Is a fresh semantic coverage enumeration required, or can the earlier
   enumeration be bridged?

## 7. Current Judgment

Current judgment:

```text
Adopt option (a).
Reject option (b) for M4 theorem design.
Forbid option (c) as circular.
```

The next implementation-level task is not full checker implementation. It is a
coverage bridge audit deciding whether the earlier 64-residual enumeration can
certify `ResidualClass` coverage for the selector-free fixed-witness semantic
universe.
