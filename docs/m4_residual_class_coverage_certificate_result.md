# M4 Certificate 1 Result: ResidualClass Coverage

Status: certificate-result / exploratory
Depends on: M4 coverage bridge audit and bundled-minlib ResidualClass design
Current authorization: Certificate 1 coverage verification only
Not authorized: Lean theorem, Certificate 2/3/4, repair-orbit checker, 3-voter run, warrant-contract implementation, paper-claim promotion

## 1. Purpose

This document records the Certificate 1 coverage result for the
bundled-minlib-aligned M4 `ResidualClass`.

The certificate enumerates all 32 bundled masks, instantiates the
selector-free fixed-witness semantic theory for each mask, and computes the
aggregate SAT/UNSAT status over the relevant witness instances.

## 2. ResidualClass Scope

The M4 `ResidualClass` is bundled-minlib-aligned.
The full 64 split universe is not the M4 `ResidualClass`.
One-sided split rows are not ambient M4 theories.

The bundled universe is fixed as:

```text
asymm
un
minlib
no_cycle3
no_cycle4
```

Case identifiers use this order:

```text
case_<asymm><un><minlib><no_cycle3><no_cycle4>
```

## 3. Semantic Instantiation Rule

Each bundled mask `T` is treated as a residual schema.

If `minlib` is inactive:

- no rights atoms are instantiated;
- `W` is inert for satisfiability of `T`;
- the semantic atom universe is the active base atoms only.

If `minlib` is active:

- `W` ranges over the 36 fixed-witness configurations
  `((voter0,P),(voter1,Q))`;
- each `W` instantiates exactly two rights atoms:
  `right(voter0,P)` and `right(voter1,Q)`.

The certificate does not instantiate one-sided rights packages and does not
create ambient theories `T` for `decisive_voter0`-only or
`decisive_voter1`-only rows.

## 4. Full 32-Mask Coverage

The run enumerated all 32 bundled masks.

Witness/status rows:

```text
16 minlib-inactive masks * 1 no-rights instance = 16
16 minlib-active masks   * 36 witness instances = 576
total witness/status rows = 592
```

Output artifacts:

```text
/tmp/sen_m4_residual_class_coverage_certificate/coverage_summary.json
/tmp/sen_m4_residual_class_coverage_certificate/mask_statuses.csv
/tmp/sen_m4_residual_class_coverage_certificate/witness_statuses.csv
/tmp/sen_m4_residual_class_coverage_certificate/boundary_formula.json
/tmp/sen_m4_residual_class_coverage_certificate/residual_class_coverage_certificate.json
```

## 5. Status Table Summary

Aggregate status counts:

| aggregate_status | count |
| --- | ---: |
| `ALL_W_SAT` | 21 |
| `ALL_W_UNSAT` | 2 |
| `MIXED` | 9 |
| `UNKNOWN` | 0 |

The `ALL_W_UNSAT` masks are exactly:

```text
case_11101
case_11111
```

The `MIXED` masks are:

```text
case_01101
case_01110
case_01111
case_10100
case_10101
case_10110
case_10111
case_11100
case_11110
```

No `UNKNOWN` mask occurred.

## 6. Boundary Formula Verdict

The tested candidate formulas produced:

| formula | verdict | note |
| --- | --- | --- |
| Candidate A | `CONDITIONAL` | No mismatching `ALL_W_UNSAT` cases, but `case_11100` and `case_11110` are `MIXED`. |
| Candidate B | `CONDITIONAL` | No mismatching `ALL_W_UNSAT` cases, but 9 masks are `MIXED`. |
| Candidate C | `FAIL` | `no_cycle3` changes aggregate status for one fixed setting of the other four levers. |

Over the `ALL_W_UNSAT` masks, the computed minimal DNF is:

```text
asymm and un and minlib and no_cycle4
```

This should not be read as a fully closed aggregate-status boundary, because
the certificate found `MIXED` masks. It is the exact boundary for masks whose
all relevant witness instances are UNSAT.

## 7. Minlib-Inactive UNSAT Absence

Result: `PASS`.

No minlib-inactive bundled mask is `ALL_W_UNSAT`.

All 16 minlib-inactive masks are `ALL_W_SAT` in this run.

## 8. No-Cycle3 Independence

Result: `FAIL` for aggregate-status independence.

The failure occurs for the fixed setting:

```text
asymm = 0
un = 1
minlib = 1
no_cycle4 = 0
```

The two `no_cycle3` variants are:

| case | no_cycle3 | aggregate_status |
| --- | ---: | --- |
| `case_01100` | 0 | `ALL_W_SAT` |
| `case_01110` | 1 | `MIXED` |

Thus `no_cycle3` is independent for the two `ALL_W_UNSAT` masks
`case_11101` and `case_11111`, but it is not independent over the full
aggregate-status table.

## 9. Relevant UNSAT Coverage

Result: `CONDITIONAL`.

The `ALL_W_UNSAT` masks in the bundled-minlib-aligned semantic enumeration
are exactly:

```text
case_11101
case_11111
```

This supports the intended relevant UNSAT coverage for the two named ambient
theories, but the presence of 9 `MIXED` masks prevents a closed Certificate 1
`PASS` under the registered aggregate-status criteria.

## 10. Finite-Auditability Interpretation

This is a complete finite enumeration over the declared
bundled-minlib-aligned `ResidualClass`.
The result is not a sample over theories.
Sen24 is the calibrated minimal-scale target, and the small finite class is
what makes the coverage certificate auditable.

Because `MIXED` masks exist, downstream theorem design must decide whether the
M4 ambient theorem scope is:

1. the two `ALL_W_UNSAT` masks only;
2. a larger semantic class with `MIXED` masks explicitly excluded by an
   additional relevance criterion; or
3. a theorem schema that accounts for `MIXED` residual theories separately.

## 11. Non-Claims

This result does not claim:

- Lean theorem;
- Certificate 2/3/4;
- orbit-fiber exactness;
- shape-blind collapse law;
- report-shape support law;
- 3-voter theorem;
- Arrow theorem;
- Gibbard-Satterthwaite theorem;
- general social-choice theorem;
- warrant-contract semantics;
- paper-ready theorem.

## 12. Certificate Verdict

Certificate verdict: `CONDITIONAL_PASS`.

Reason:

```text
MIXED status exists; candidate formula A is CONDITIONAL; candidate formula B is
CONDITIONAL; candidate formula C is FAIL; relevant UNSAT coverage is
CONDITIONAL.
```

The certificate establishes:

- all 32 bundled masks were enumerated;
- no `UNKNOWN` occurred;
- no minlib-inactive mask is `ALL_W_UNSAT`;
- the only `ALL_W_UNSAT` masks are `case_11101` and `case_11111`;
- the exact `ALL_W_UNSAT` boundary is
  `asymm and un and minlib and no_cycle4`.

The certificate does not establish:

- full aggregate-status no-cycle3 independence;
- a `PASS` verdict for Candidate Formula B under the registered rule that any
  `MIXED` mask prevents a formula from passing;
- closed Certificate 1 coverage for theorem promotion.

## 13. Next Authorized Action

Next authorized action: resolve the M4 theorem scope for `MIXED` residual
theories before implementing Certificate 2.

The immediate design question is whether `ResidualClass` for Theorem A/B/C
should quantify only over the two `ALL_W_UNSAT` ambient theories or whether a
separate semantic relevance criterion must be certified for excluding `MIXED`
masks.

## 14. Follow-up

The MIXED masks motivated a mask-shape collapse audit.
See `docs/m4_mask_shape_collapse_law_audit_result.md`.

This follow-up does not upgrade the Certificate 1 verdict. Certificate 1
remains `CONDITIONAL_PASS` under its registered aggregate-status criteria.
