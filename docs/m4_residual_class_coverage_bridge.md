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

## 6. Full Split Universe vs M4 ResidualClass

The full split universe is a representation-level upstream artifact. It has
six independent levers:

```text
asymm
un
decisive_voter0
decisive_voter1
no_cycle3
no_cycle4
```

Therefore the full 64 split residual universe includes one-sided masks where
exactly one of `decisive_voter0` or `decisive_voter1` is active.

Examples of one-sided split residuals include:

- `case_110101` / `case_111001`, depending on retained/deleted convention;
- rows where `decisive_voter0` and `decisive_voter1` do not have the same
  active/inactive status.

These are valid split-representation residuals in the full 64 split universe.

The full 64 split universe is not the M4 ambient `ResidualClass`.

## 7. Bundled-Minlib-Aligned M4 ResidualClass

The M4 `ResidualClass` is not the full independent 64-bit split universe.

For M4, `T` is a residual schema determined by active residual levers/axiom
masks at the bundled-minlib semantic level.

In particular:

- `minlib` is a `T`-level bundled schema;
- `W` is internal to `T`;
- when `minlib` is active, `W` instantiates a two-person rights package;
- the instantiated selector-free semantic rights atoms are generated inside
  `T` after `W` is chosen.

Distinction:

```text
Full split universe:
  decisive_voter0 and decisive_voter1 are independent representation-level
  split levers.

M4 bundled-minlib semantic ResidualClass:
  minlib is a bundled T-level schema.
  It does not create one ambient T for decisive_voter0 alone and another
  ambient T for decisive_voter1 alone.
  It creates internal W-instances of a two-person rights schema.
```

## 8. One-Sided Split Residuals Are Not M4 Ambient Theories

One-sided split residuals such as `decisive_voter0`-only or
`decisive_voter1`-only rows are valid artifacts of the full split
representation universe.

They are not ambient residual theories `T` in the M4 bundled-minlib semantic
`ResidualClass`.

They are excluded from M4 `ResidualClass` not because they would violate or
satisfy Theorem C, but because they do not correspond to a valid bundled
`minlib` schema instantiation.

This exclusion must be justified by the prior definition of bundled `minlib`,
not by any observed orbit-fiber exactness, shape support, or Report-Shape
Support Collapse Law.

Therefore:

```text
valid reason: bundled minlib schema requires the two-person liberalism package;
invalid reason: one-sided rows are excluded because Theorem C would fail or
                because shape support would be unstable.
```

## 9. Structural Interpretation: Two-Person Liberalism as Common Source

The same Sen liberalism structure appears on two sides of the design:

1. Coverage side:
   bundled `minlib` is a two-person schema, so one-sided split rows are not
   ambient M4 residual theories.
2. Repair-geometry side:
   `minlib` has support across O2/O3/O4 and produces maximal shape-blind
   collapse in the Phase 2 diagnostic.

This suggests a common structural source:

```text
the two-person nature of Sen liberalism drives both the bundled-minlib
coverage boundary and the observed minlib collapse behavior.
```

This is a structural interpretation, not yet an additional theorem. The
coverage exclusion is certified by the `minlib` schema definition. The collapse
behavior is certified by Phase 2 diagnostics. A later checker may test whether
both are derived from the same schema-level datum.

## 10. Immediate Next Audit Questions

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
9. Are one-sided split residuals present in the full split universe?
10. Are one-sided split residuals ever instantiated as ambient M4 residual
    theories `T`?
11. Is their exclusion justified solely by bundled `minlib` schema definition?
12. Does the bundled `minlib` schema require a two-person witness package?
13. Can the checker derive both:
    (a) one-sided exclusion, and
    (b) `minlib` O2/O3/O4 support,
    from the same schema-level `minlib` datum?

## 11. Current Judgment

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
