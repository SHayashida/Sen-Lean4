# M3 Candidate B GroupSoundness Audit Plan

## 1. Purpose

The goal is to determine, using existing Candidate B artifacts if possible,
whether the M1.5 Candidate B split realization satisfies the assumptions of
M3-B relative to the bundled-level reportability contract.

The intended conclusion, if the audit passes, is that the same witness
supports:

- M1.5 raw-level non-canonicity; and
- M3-B contract-level grouped report correctness.

This does not erase the M1.5 result. It refines it: raw repairs may be
non-canonical across bundled and split implementations while grouped reports
are canonical under an explicitly verified reportability contract.

This document specifies an artifact-only audit. It does not perform the audit
and authorizes no new solver execution.

## 2. Contract Instantiation and Scope

For this audit, the bundled-level reportability contract `C_b` is instantiated
by the bundled encoding residuals recorded in the Candidate B artifacts. That
is, `Psi_b(T)` is represented by the bundled residual for active atom set `T`.

This is an artifact-defined contract for the declared Candidate B scope. No
semantic validity beyond that scope is claimed.

Bundled-level active atoms:

```text
I = {asymm, un, minlib, no_cycle4}
```

Split realization interface:

```text
Lambda_I = {asymm, un, decisive_voter0, decisive_voter1, no_cycle4}
```

Block map:

```text
beta(asymm) = {asymm}
beta(un) = {un}
beta(minlib) = {decisive_voter0, decisive_voter1}
beta(no_cycle4) = {no_cycle4}
```

Touch-any grouping:

```text
group({asymm}) = {asymm}
group({un}) = {un}
group({decisive_voter0}) = {minlib}
group({decisive_voter1}) = {minlib}
group({no_cycle4}) = {no_cycle4}
```

## 3. Fully Active UNSAT Prerequisite

Before checking repairs, the audit must establish the non-degenerate repair
setting:

- the bundled fully active residual is UNSAT;
- the split fully active residual is UNSAT.

Expected artifact keys or cases should be recorded, for example:

```text
Bundled fully active: case_11101 or corresponding bundled case identifier
Split fully active:   case_111101 or corresponding split case identifier
```

These names are provisional. The audit must record the exact artifact source,
case identifier, active set, and status rather than assuming the identifiers.

If either fully active residual is SAT or unknown, the audit fails for the
non-degenerate repair claim.

## 4. Target Theorem Assumptions

M3-B requires:

```text
ResidualFaithfulness(E_s, C_b)
and
GroupSoundness(E_s, C_b).
```

The audit therefore has two independent obligations:

1. block-aligned residual status agreement; and
2. grouped soundness of implementation-level raw repairs.

The second obligation may use the audit-cost collapse lemma only after
`PsiDeletionMonotonicity(C_b)` and raw-repair completeness have been
established.

## 4.5 Residual Faithfulness Audit

The condition is:

```text
ResidualFaithfulness(E_s, C_b) :iff
  for every T subseteq I,
    SAT(phi_s(B_s, beta(T))) iff SAT(Psi_b(T)).
```

Since `|I| = 4`, this requires 16 block-aligned residual comparisons.

The audit should inspect existing Candidate B mapped-comparison artifacts
first. If a 32-case bundled-to-split mapped comparison artifact already
records status preservation, the audit should extract the 16 block-aligned
cases from it and record how each row was selected.

| T subseteq I | Bundled residual Psi_b(T) status | Split block-aligned beta(T) status | Artifact source | Direct or extracted | Match? |
| --- | --- | --- | --- | --- | --- |
| empty | TBD | TBD | TBD | TBD | TBD |
| {asymm} | TBD | TBD | TBD | TBD | TBD |
| {un} | TBD | TBD | TBD | TBD | TBD |
| {minlib} | TBD | TBD | TBD | TBD | TBD |
| {no_cycle4} | TBD | TBD | TBD | TBD | TBD |
| {asymm,un} | TBD | TBD | TBD | TBD | TBD |
| {asymm,minlib} | TBD | TBD | TBD | TBD | TBD |
| {asymm,no_cycle4} | TBD | TBD | TBD | TBD | TBD |
| {un,minlib} | TBD | TBD | TBD | TBD | TBD |
| {un,no_cycle4} | TBD | TBD | TBD | TBD | TBD |
| {minlib,no_cycle4} | TBD | TBD | TBD | TBD | TBD |
| {asymm,un,minlib} | TBD | TBD | TBD | TBD | TBD |
| {asymm,un,no_cycle4} | TBD | TBD | TBD | TBD | TBD |
| {asymm,minlib,no_cycle4} | TBD | TBD | TBD | TBD | TBD |
| {un,minlib,no_cycle4} | TBD | TBD | TBD | TBD | TBD |
| {asymm,un,minlib,no_cycle4} | TBD | TBD | TBD | TBD | TBD |

Pass this obligation only if all 16 status comparisons match.

If any comparison is missing, unknown, or mismatched, the audit cannot
instantiate M3-B without additional evidence.

## 5. Psi-Deletion-Monotonicity Justification

The bundled-level contract is expected to be a standard conjunctive
axiom-deletion contract: deleting a contract atom removes constraints.

Therefore `PsiDeletionMonotonicity(C_b)` should hold:

```text
for all T' subseteq T subseteq I,
  SAT(Psi_b(T)) implies SAT(Psi_b(T')).
```

This must not be assumed silently. The audit must record one of:

- direct artifact evidence that bundled residual SAT status is
  deletion-monotone over the relevant subset lattice; or
- a documented construction argument that bundled residuals are produced by
  clause-family deletion, so deleting atoms weakens the CNF.

This is monotonicity of `Psi_b`, not deletion-monotonicity of `phi_s`.

## 6. RawRep Completeness Audit

The audit-cost collapse lemma reduces GroupSoundness checking to raw minimal
repairs only if the raw repair family is completely identified. The audit must
prove:

```text
RawRep(E_s) =
{
  {asymm},
  {un},
  {decisive_voter0},
  {decisive_voter1},
  {no_cycle4}
}.
```

Use the following completeness argument.

First, confirm from existing split artifacts that each singleton deletion is
SAT:

```text
{asymm}
{un}
{decisive_voter0}
{decisive_voter1}
{no_cycle4}
```

Second, confirm that the fully active split residual is UNSAT, so the empty
deletion is not a repair.

Third, confirm that `Lambda_I` consists exactly of those five active levers.
Every nonempty deletion `R` then contains at least one singleton deletion. If
`|R| > 1`, it properly contains a confirmed singleton repair and therefore
cannot be inclusion-minimal.

Thus the five confirmed singleton repairs exhaust `RawRep(E_s)`.

| Split singleton deletion R | Split residual status | Artifact source | Result |
| --- | --- | --- | --- |
| {asymm} | SAT | TBD | TBD |
| {un} | SAT | TBD | TBD |
| {decisive_voter0} | SAT | TBD | TBD |
| {decisive_voter1} | SAT | TBD | TBD |
| {no_cycle4} | SAT | TBD | TBD |

## 7. GroupSoundness Audit via Audit-Cost Collapse

The target condition is:

```text
GroupSoundness(E_s, C_b) :iff
  for every R subseteq Lambda_I,
    SAT(phi_s(B_s, Lambda_I \ R))
    implies
    SAT(Psi_b(I \ group_s(R))).
```

Under `PsiDeletionMonotonicity(C_b)`, and once `RawRep(E_s)` is completely
identified, it is enough to check:

```text
for every R in RawRep(E_s),
  SAT(Psi_b(I \ group_s(R))).
```

| Split raw repair R | group_s(R) | Bundled residual I \ group_s(R) | Required bundled status | Artifact source | Direct or inferred | Result |
| --- | --- | --- | --- | --- | --- | --- |
| {asymm} | {asymm} | {un,minlib,no_cycle4} | SAT | TBD | TBD | TBD |
| {un} | {un} | {asymm,minlib,no_cycle4} | SAT | TBD | TBD | TBD |
| {decisive_voter0} | {minlib} | {asymm,un,no_cycle4} | SAT | TBD | TBD | TBD |
| {decisive_voter1} | {minlib} | {asymm,un,no_cycle4} | SAT | TBD | TBD | TBD |
| {no_cycle4} | {no_cycle4} | {asymm,un,minlib} | SAT | TBD | TBD | TBD |

The two decisive-voter rows map to the same bundled contract repair
`{minlib}`.

## 8. Required Artifact Fields

Inspect existing Candidate B artifacts first, especially:

```text
results/20260401/candidate_b_minlib_granularity/summary.md
results/20260401/candidate_b_minlib_granularity/comparison.json
```

If these paths differ, record the actual paths found.

For every cited status, record:

- artifact source path;
- case identifier;
- residual active atom set or deletion set;
- SAT/UNSAT status;
- whether the status is directly recorded or extracted from a comparison
  table;
- whether any conclusion uses monotonicity inference.

No solver execution should occur in this plan.

## 9. Pass / Fail Criteria

### Pass

Pass only if all six conditions hold:

1. Fully active bundled and split residuals are both UNSAT in existing
   artifacts.
2. The five split singleton repairs are SAT in existing artifacts, and
   singleton dominance proves `RawRep(E_s)` is exactly the five singleton
   repairs.
3. The five grouped reports all map to bundled residuals that are SAT,
   establishing GroupSoundness via audit-cost collapse.
4. The 16 block-aligned residual status comparisons match, establishing
   `ResidualFaithfulness(E_s, C_b)`.
5. `PsiDeletionMonotonicity(C_b)` is justified either by direct artifact
   evidence or by clause-family deletion construction.
6. No new solver run is required.

### Fail

Fail if any of the following occurs:

- either fully active residual is SAT or unknown;
- any singleton repair status is missing or not SAT;
- singleton dominance cannot be applied because `Lambda_I` has additional
  active levers;
- any required bundled residual is UNSAT or unknown;
- any of the 16 residual faithfulness comparisons is missing or mismatched;
- `PsiDeletionMonotonicity(C_b)` cannot be justified;
- the audit requires new solving rather than artifact reanalysis.

## 10. Interpretation if Pass

If the audit passes, state:

> The Candidate B witness simultaneously supports:
>
> - M1.5 raw-level non-canonicity; and
> - M3-B contract-level grouped report correctness.

More precisely, raw repairs are non-canonical across bundled and split
implementations, but under the bundled-level artifact-defined contract `C_b`,
verified residual faithfulness, verified GroupSoundness, and touch-any
grouping, the grouped repair report is canonical.

Do not claim that M1.5 is erased or invalidated. A pass refines M1.5 by
separating raw-level non-canonicity from contract-level reportability.

## 11. Interpretation if Fail

If the audit fails, state:

> M3-B remains a valid theorem skeleton, but Candidate B does not instantiate
> it under the declared bundled-level contract without additional evidence, a
> different reportability contract, or a new audit run.

Do not weaken M3-B to rescue Candidate B in this document.

## 12. Acceptance Criteria

- Create exactly one file:
  `docs/m3_candidate_b_group_soundness_audit_plan.md`.
- Make no code changes.
- Run no solver.
- Add no Arrow, M4, DAO, AI-governance, or six-layer material.
- Keep this document as an audit plan, not an audit result.
- Include the fully active UNSAT prerequisite.
- Declare the contract instantiation.
- Include the residual faithfulness audit.
- Include the raw repair completeness argument.
- Include the GroupSoundness audit table.
- Include the six-condition pass criteria.
