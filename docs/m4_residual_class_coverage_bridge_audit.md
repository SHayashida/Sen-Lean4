# M4 Coverage Bridge Audit: Bundled-Minlib ResidualClass

Status: audit-result / design-only
Depends on: M4 ResidualClass individuation decision and full split vs bundled-minlib separation
Current authorization: coverage bridge audit using existing artifacts
Not authorized: solver rerun, Lean implementation, checker implementation, 3-voter run, warrant-contract implementation, paper-claim promotion

## Audit Questions

### Q1. What is the full split universe mask vocabulary?

Finding: the full split universe is an upstream representation-level artifact
with six independent levers:

```text
asymm
un
decisive_voter0
decisive_voter1
no_cycle3
no_cycle4
```

Evidence:

- `scripts/run_candidate_b_minlib_granularity.py` defines
  `SPLIT_UNIVERSE` with these six levers.
- `docs/m3_canonical_integration_precheck.md` records the split universe as
  `[asymm, un, decisive_voter0, decisive_voter1, no_cycle3, no_cycle4]`.

### Q2. What is the bundled universe mask vocabulary?

Finding: the bundled universe has five levers:

```text
asymm
un
minlib
no_cycle3
no_cycle4
```

Evidence:

- `scripts/run_candidate_b_minlib_granularity.py` defines
  `BUNDLED_UNIVERSE` with these five levers.
- `docs/m3_canonical_integration_precheck.md` records the bundled universe as
  `[asymm, un, minlib, no_cycle3, no_cycle4]`.

### Q3. What is the bundled-minlib-aligned sublattice?

Finding: bundled `minlib` maps to the paired split package:

```text
minlib -> {decisive_voter0, decisive_voter1}
```

Therefore the bundled-to-split block-aligned sublattice is not the full 64
split universe. It is the subset where the two split decisive levers move
together as the image of bundled `minlib`.

Evidence:

- `scripts/run_candidate_b_minlib_granularity.py` implements
  `_bundled_to_split_axioms`, replacing active `minlib` by both split decisive
  levers.
- `docs/m3_canonical_integration_precheck.md` audits the 16 block-aligned rows
  in the no-cycle3-off Candidate B contract lattice.

This sublattice is justified by the prior bundled-minlib schema definition,
not by Theorem C.

### Q4. Does the aligned sublattice definition predate M4 Theorem C?

Finding: yes. The bundled-to-split block-alignment appears in M1.5/M3/Candidate
B granularity artifacts before the M4 Theorem C design.

Read-only provenance commands:

```text
git log --follow --oneline -- docs/m3_canonical_integration_precheck.md
  e36c398 docs(m3): precheck selective canonical integration

git log --follow --oneline -- scripts/run_candidate_b_minlib_granularity.py
  9f6c429 Integrate M1.5 and M2 transfer contract artifacts

git log --oneline --all --grep="minlib"
  890952f M2.1: add Candidate-B encoding-sensitivity witness-class memo
  aa2e2c4 Add Candidate B minlib granularity experiment
  d980710 Complete Step 3: local minimality checks - Outcome A, all repairs locally minimal

git log --oneline --all --grep="candidate b"
  no hits
```

M4 theorem-design commits are later local commits, including:

```text
1642a96 docs: design obstruction-indexed repair-orbit classification
0873cf8 docs: parameterize M4 orbit classification by ambient residual theory
05b68a3 docs: define M4 residual class coverage bridge
79a290f docs: separate full split universe from M4 residual class
```

Provenance verdict:

- PASS if bundled-minlib alignment is present in pre-M4 artifacts.
- CONDITIONAL if present but commit chronology is unclear.
- FAIL if alignment was introduced only after M4 Theorem C was formulated.

Actual verdict: PASS. The Candidate B artifacts and M3 precheck precede the M4
Theorem C design commits in the inspected history.

### Q5. Are one-sided split rows present in the full split universe?

Finding: yes. The full split universe contains one-sided rows where
`decisive_voter0` and `decisive_voter1` differ.

The full split universe contains one-sided rows where `decisive_voter0` and
`decisive_voter1` differ. Examples include rows corresponding to one-sided
deletion/retention such as `case_110101` and `case_111001`, depending on
retained/deleted convention.

Evidence:

- `scripts/run_candidate_b_minlib_granularity.py` explicitly collects
  `one_sided_split_cases` by checking whether exactly one decisive split lever
  is active.
- `docs/m3_canonical_integration_precheck.md` lists `case_110101` and
  `case_111001` as non-block-aligned singleton split cases.

These one-sided rows are valid split-representation residuals in the full 64
split universe. They are not ambient M4 residual theories `T`.

### Q6. Are one-sided split rows ambient M4 residual theories T?

Finding: no for the current M4 design scope.

They are valid split-representation residuals, but they are not valid
instantiations of the bundled-minlib semantic schema used to define M4 ambient
theories.

Implementation-level certificate note: the intended design treats one-sided
rows as non-instantiations of bundled `minlib`; a future checker should still
verify this from the schema mapping rather than from downstream orbit
behavior.

### Q7. What is the exclusion basis for one-sided split rows?

Finding: one-sided rows are excluded from M4 `ResidualClass` because they are
not valid bundled-minlib semantic residual schemas.

They are not excluded because Theorem C would fail.
They are not excluded because shape support would be unstable.
They are not excluded because they are inconvenient.

Valid exclusion basis:

```text
bundled minlib is a T-level schema requiring a two-person liberalism package.
```

Invalid exclusion basis:

```text
excluding one-sided rows by appeal to orbit-fiber exactness,
ShapeSupport_T, or Report-Shape Support Collapse Law.
```

### Q8. Do case_11101 and case_11111 name residual masks/schemas rather than witness configurations?

Finding: yes. `case_11101` and `case_11111` should be treated as named
residual masks/schemas, not witness configurations.

Evidence:

- `docs/m3_canonical_integration_precheck.md` fixes bundled bit order as
  `[asymm, un, minlib, no_cycle3, no_cycle4]` and identifies `case_11101` as
  `{asymm, un, minlib, no_cycle4}`.
- `docs/m4_semantic_mus_precheck_result.md` identifies `case_11101` and
  `case_11111` as target residual cases with `minlib` replaced by fixed rights
  atoms only after the case is selected.
- `docs/m4_repair_orbit_precheck_result.md` defines repair objects as
  `(target_case, W, R)` with `target_case in {case_11101, case_11111}`, making
  `W` an internal component rather than part of the case identifier.

### Q9. Does minlib behave as a T-level bundled schema whose rights atoms are generated only after W is chosen?

Finding: yes for the M4 design artifacts.

The M4 semantic precheck and repair-orbit precheck treat `minlib` as a
residual-case-level bundled schema. For each fixed `target_case`, the
fixed-witness instantiation replaces the bundled schema by
`right(voter0,P)` and `right(voter1,Q)` after a witness `W` is chosen.

This is the basis for treating `W` as internal to `T` and for refusing to turn
one-sided split rows into separate M4 ambient theories.

### Q10. Does the bundled-minlib-aligned ResidualClass have relevant UNSAT coverage exhausted by case_11101 and case_11111?

Finding: CONDITIONAL.

Current artifacts support `case_11101` and `case_11111` as the two named
UNSAT ambient theories used by the M4 semantic and repair-orbit diagnostics.
They also support the prior bundled-minlib alignment and distinguish it from
the full split representation universe. However, a semantic-level coverage
certificate is still required to close finite-universal coverage for the M4
`ResidualClass`.

CONDITIONAL: current artifacts support the two named UNSAT ambient theories,
but a semantic-level coverage certificate is still required to close
finite-universal coverage.

This is a finite-auditability condition, not a sampling claim. The class is
finite by construction, and Sen24 is the calibrated minimal-scale target. If
the audit verifies that the enumeration is complete, then two UNSAT ambient
theories are a complete finite result, not a sample.

### Q11. Which parts are Sen-specific, and which parts are reusable methodology?

Finding: the bridge mixes a Sen-specific schema boundary with a reusable audit
pattern.

Sen-specific:

- bundled `minlib` is a two-person liberalism schema;
- one-sided decisive-voter rows are not M4 ambient theories;
- `minlib` spans O2/O3/O4 in the Phase 2 diagnostic;
- `case_11101` and `case_11111` are the named Sen24 ambient theories currently
  carrying the nontrivial UNSAT result.

Reusable methodology:

- distinguish upstream representation universe from semantic ambient
  `ResidualClass`;
- individuate `T` independently of `W`;
- ensure exclusions are justified by schema definitions, not by target
  theorems;
- require provenance showing that the schema mapping predates the theorem;
- treat small finite classes as auditability conditions, not samples;
- separate coverage, exactness, collapse, and support-law certificates.

## Full Split Universe

The full split universe is an upstream representation-level artifact with six
independent levers:

```text
asymm
un
decisive_voter0
decisive_voter1
no_cycle3
no_cycle4
```

The full split universe contains 64 masks. Because `decisive_voter0` and
`decisive_voter1` are independent in that representation, this universe
contains one-sided split rows.

## Bundled Universe

The bundled universe has five levers:

```text
asymm
un
minlib
no_cycle3
no_cycle4
```

The bundled universe contains 32 masks. The M4 ambient theorem scope is not
the full 32-mask lattice as a paper claim; it is the bundled-minlib-aligned
semantic residual schema class whose relevant UNSAT part is currently carried
by the named cases `case_11101` and `case_11111`, subject to the finite
coverage certificate.

## Bundled-Minlib-Aligned Sublattice

Bundled `minlib` maps to the paired split package:

```text
minlib -> {decisive_voter0, decisive_voter1}
```

Therefore the bundled-to-split block-aligned sublattice is not the full 64
split universe. It is the subset where the two split decisive levers move
together as the image of bundled `minlib`.

This sublattice is justified by the prior bundled-minlib schema definition,
not by Theorem C.

## One-Sided Split Rows

The full split universe contains one-sided rows where `decisive_voter0` and
`decisive_voter1` differ. Examples include rows corresponding to one-sided
deletion/retention such as `case_110101` and `case_111001`, depending on
retained/deleted convention.

These one-sided rows are valid split-representation residuals in the full 64
split universe.
They are not ambient M4 residual theories `T`.

## One-Sided Exclusion Basis

One-sided rows are excluded from M4 `ResidualClass` because they are not valid
bundled-minlib semantic residual schemas.

They are not excluded because Theorem C would fail.
They are not excluded because shape support would be unstable.
They are not excluded because they are inconvenient.

Valid exclusion basis:

```text
bundled minlib is a T-level schema requiring a two-person liberalism package.
```

Invalid exclusion basis:

```text
excluding one-sided rows by appeal to orbit-fiber exactness,
ShapeSupport_T, or Report-Shape Support Collapse Law.
```

The most accurate current judgment is:

```text
They are valid split-representation residuals, but they are not valid
instantiations of the bundled-minlib semantic schema used to define M4 ambient
theories.
```

## Provenance / Non-Circularity Audit

The bundled-to-split block-alignment appears in M1.5/M3/Candidate B
granularity artifacts before the M4 Theorem C design.

The decisive evidence is chronological and structural:

- `aa2e2c4 Add Candidate B minlib granularity experiment` introduced the
  Candidate B granularity experiment before the M4 Phase 2 branch.
- `9f6c429 Integrate M1.5 and M2 transfer contract artifacts` is the current
  history source for `scripts/run_candidate_b_minlib_granularity.py`.
- `e36c398 docs(m3): precheck selective canonical integration` records the M3
  precheck, including bundled and split universes, 16 block-aligned rows, and
  the two non-block-aligned singleton split cases.
- M4 Theorem C design appears later in the local M4 design commits.

Provenance verdict:

```text
PASS
```

The block-aligned sublattice was not created by looking at the M4 support
collapse law. It was already present as a Candidate B/M3 representation
mapping.

## Relevant UNSAT Coverage

Within the bundled-minlib-aligned M4 design artifacts, `case_11101` and
`case_11111` are the named UNSAT ambient theories carrying the Phase 1 and
Phase 2 semantic diagnostics.

This audit does not promote that observation to a closed Lean theorem or paper
claim. It records the current bridge status:

```text
CONDITIONAL: current artifacts support the two named UNSAT ambient theories,
but a semantic-level coverage certificate is still required to close
finite-universal coverage.
```

This is a finite-auditability condition, not a sampling claim. The class is
finite by construction, and Sen24 is the calibrated minimal-scale target. If
the audit verifies that the enumeration is complete, then two UNSAT ambient
theories are a complete finite result, not a sample.

## Sen-Specific Boundary vs Reusable Methodology

Sen-specific:

- bundled `minlib` is a two-person liberalism schema;
- one-sided decisive-voter rows are not M4 ambient theories;
- `minlib` spans O2/O3/O4 in the Phase 2 diagnostic;
- `case_11101` and `case_11111` are the named Sen24 ambient theories currently
  carrying the nontrivial UNSAT result.

Reusable methodology:

- distinguish upstream representation universe from semantic ambient
  `ResidualClass`;
- individuate `T` independently of `W`;
- ensure exclusions are justified by schema definitions, not by target
  theorems;
- require provenance showing that the schema mapping predates the theorem;
- treat small finite classes as auditability conditions, not samples;
- separate coverage, exactness, collapse, and support-law certificates.

## Bounded Structural Interpretation

The two-person structure of Sen liberalism appears to explain both:

1. why one-sided split rows are not bundled-minlib M4 ambient theories; and
2. why `minlib` produces maximal shape-blind collapse across O2/O3/O4 in the
   Phase 2 diagnostic.

This is a structural interpretation, not an additional theorem.

The coverage exclusion is certified by the bundled-minlib schema definition.
The collapse behavior is certified by Phase 2 diagnostics.
A later checker may test whether both are derived from the same schema-level
datum.

## Audit Verdict

CONDITIONAL PASS:

- full split universe and M4 `ResidualClass` are distinguished;
- bundled-minlib-aligned sublattice has pre-M4 provenance;
- one-sided rows are valid upstream split artifacts but not ambient M4
  theories;
- one-sided exclusion is justified by bundled `minlib` schema, not Theorem C;
- `case_11101`/`case_11111` are named residual schemas, not `W`;
- relevant UNSAT coverage is framed as finite-auditability rather than
  sampling.

The pass is conditional only because a future semantic-level coverage
certificate is still required to close finite-universal coverage for the M4
`ResidualClass`.
