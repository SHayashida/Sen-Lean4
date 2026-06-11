# M3 Candidate B GroupSoundness Audit Result

## 1. Purpose

This document executes
[`docs/m3_candidate_b_group_soundness_audit_plan.md`](m3_candidate_b_group_soundness_audit_plan.md)
and determines whether the M1.5 Candidate B split realization instantiates
M3-B relative to the bundled-level artifact-defined contract `C_b`.

This audit checks:

1. fully active UNSAT;
2. implementation-deletion-closure;
3. residual faithfulness;
4. `PsiDeletionMonotonicity`;
5. `RawRep` completeness;
6. `GroupSoundness` via audit-cost collapse.

Only existing Candidate B artifacts were read. No solver was run and no
experimental artifact was created.

## 2. Artifact Sources Inspected

The short names used in later tables refer to the full paths below.

| Path | Role | Sufficient? | Missing expected field? |
| --- | --- | --- | --- |
| `results/20260401/candidate_b_minlib_granularity/summary.md` | Human-readable experiment overview, frontier counts, witness packages, and minimal repairs | Sufficient as an overview; not sufficient alone for the 16-row audit | No bit-to-lever table or per-case mapped rows |
| `results/20260401/candidate_b_minlib_granularity/comparison.json` | Primary evidence: ordered universes, 32 mapped cases, statuses, package lists, clause-multiset comparison, one-sided split cases, and bundled/split minimal repairs | Yes | No missing field needed by this audit |
| `results/20260401/candidate_b_minlib_granularity/comparison.csv` | Independent tabular cross-check of the two repair-comparison witnesses | Yes, for repair-record cross-check only | Does not contain the full mapped frontier |
| `results/20260401/candidate_b_minlib_granularity/bundled/atlas.json` | Complete 32-case bundled atlas, ordered universe, active/off sets, case masks, and statuses | Yes | No |
| `results/20260401/candidate_b_minlib_granularity/split/atlas.json` | Complete 64-case split atlas, ordered universe, active/off sets, case masks, and statuses | Yes | No |
| `results/20260401/candidate_b_minlib_granularity/bundled/case_11101/summary.json` | Direct fully active bundled case status and active/off sets | Yes | No |
| `results/20260401/candidate_b_minlib_granularity/split/case_111101/summary.json` | Direct fully active split case status and active/off sets | Yes | No |
| `results/20260401/candidate_b_minlib_granularity/bundled/case_11101/sen24.manifest.json` | Bundled witness clause categories and CNF hash | Partially; used as a construction cross-check | The legacy manifest has no explicit `axioms` field; the case summary supplies the active set |
| `results/20260401/candidate_b_minlib_granularity/split/case_111101/sen24.manifest.json` | Split witness active axioms, clause categories, schema, and CNF hash | Yes | No |
| `results/20260401/candidate_b_minlib_granularity/split/case_011101/summary.json` | Split residual after deleting `asymm` | Yes | No |
| `results/20260401/candidate_b_minlib_granularity/split/case_101101/summary.json` | Split residual after deleting `un` | Yes | No |
| `results/20260401/candidate_b_minlib_granularity/split/case_110101/summary.json` | Split residual after deleting `decisive_voter0` | Yes | No |
| `results/20260401/candidate_b_minlib_granularity/split/case_111001/summary.json` | Split residual after deleting `decisive_voter1` | Yes | No |
| `results/20260401/candidate_b_minlib_granularity/split/case_111100/summary.json` | Split residual after deleting `no_cycle4` | Yes | No |

The primary target paths existed exactly as specified.

## 2.5 Case Identifier and Mapping Conventions

The ordered universes are recorded in `comparison.json` and repeated as
`axiom_universe` in the two atlas files.

Bundled case bit order:

```text
[asymm, un, minlib, no_cycle3, no_cycle4]
```

Split case bit order:

```text
[asymm, un, decisive_voter0, decisive_voter1, no_cycle3, no_cycle4]
```

A bit is `1` exactly when the corresponding lever is active. Therefore:

- bundled `no_cycle3` is bit 4;
- split `no_cycle3` is bit 5;
- bundled contract atoms occupy bits 1, 2, 3, and 5;
- split interface levers occupy bits 1, 2, 3, 4, and 6.

Worked examples:

```text
case_11101
-> [asymm=1, un=1, minlib=1, no_cycle3=0, no_cycle4=1]
-> active {asymm, un, minlib, no_cycle4}

case_111101
-> [asymm=1, un=1, decisive_voter0=1, decisive_voter1=1,
    no_cycle3=0, no_cycle4=1]
-> active {asymm, un, decisive_voter0, decisive_voter1, no_cycle4}
```

Both decodings are confirmed by the explicit package and `axioms_on` fields in
`comparison.json` and the corresponding case summaries.

### no_cycle3 filter

For every `T subseteq I`, where:

```text
I = {asymm, un, minlib, no_cycle4},
```

the audited mapped case has `no_cycle3 = 0`. The four contract atoms are set
according to `T`; on the split side, `minlib = 1` maps to both decisive-voter
bits being `1`. Every row in Section 4 has `0` in the documented
`no_cycle3` position.

### Evidence classification rule

This result uses:

- `direct (via enumeration record)` for membership in
  `bundled_min_repairs` or `split_min_repairs`;
- `direct` for a SAT/UNSAT status explicitly recorded in a mapped case, atlas
  case, or case summary;
- `inferred` for conclusions obtained by monotonicity, singleton dominance,
  audit-cost collapse, or another reasoning step.

## 3. Fully Active UNSAT Prerequisite

| Side | Case identifier | Active set / deletion set | Status | Artifact source | Result |
| --- | --- | --- | --- | --- | --- |
| bundled | `case_11101` | active `{asymm,un,minlib,no_cycle4}`; deletion `empty` | UNSAT | `comparison.json`; `bundled/atlas.json`; `bundled/case_11101/summary.json` | PASS |
| split | `case_111101` | active `{asymm,un,decisive_voter0,decisive_voter1,no_cycle4}`; deletion `empty` | UNSAT | `comparison.json`; `split/atlas.json`; `split/case_111101/summary.json` | PASS |

Both statuses are direct and agree across the primary comparison, atlas, and
case-summary records. The non-degenerate repair prerequisite passes.

## 3.5 Implementation-Deletion-Closure Note

`split/atlas.json` records the ordered six-lever split universe and all
`64 = 2^6` subsets. Restricting `no_cycle3` to `0` leaves all
`32 = 2^5` residuals over:

```text
Lambda_I =
  {asymm, un, decisive_voter0, decisive_voter1, no_cycle4}.
```

Each case has a generated CNF reference and a recorded status. Therefore the
artifact construction defines a residual CNF for every subset of the declared
five-lever implementation interface. Implementation-deletion-closure passes
directly from `split/atlas.json`.

## 4. Residual Faithfulness Audit

Every row below is a direct mapped-case record from `comparison.json`.
`Bundled case id` and `Split block-aligned case id` both keep
`no_cycle3 = 0`.

| T subseteq I | Bundled case id | Split block-aligned case id | Bundled residual Psi_b(T) status | Split block-aligned beta(T) status | Artifact source | Direct/extracted/inferred | Match? |
| --- | --- | --- | --- | --- | --- | --- | --- |
| empty | `case_00000` | `case_000000` | SAT | SAT | `comparison.json` mapped case | direct | PASS |
| {asymm} | `case_10000` | `case_100000` | SAT | SAT | `comparison.json` mapped case | direct | PASS |
| {un} | `case_01000` | `case_010000` | SAT | SAT | `comparison.json` mapped case | direct | PASS |
| {minlib} | `case_00100` | `case_001100` | SAT | SAT | `comparison.json` mapped case | direct | PASS |
| {no_cycle4} | `case_00001` | `case_000001` | SAT | SAT | `comparison.json` mapped case | direct | PASS |
| {asymm,un} | `case_11000` | `case_110000` | SAT | SAT | `comparison.json` mapped case | direct | PASS |
| {asymm,minlib} | `case_10100` | `case_101100` | SAT | SAT | `comparison.json` mapped case | direct | PASS |
| {asymm,no_cycle4} | `case_10001` | `case_100001` | SAT | SAT | `comparison.json` mapped case | direct | PASS |
| {un,minlib} | `case_01100` | `case_011100` | SAT | SAT | `comparison.json` mapped case | direct | PASS |
| {un,no_cycle4} | `case_01001` | `case_010001` | SAT | SAT | `comparison.json` mapped case | direct | PASS |
| {minlib,no_cycle4} | `case_00101` | `case_001101` | SAT | SAT | `comparison.json` mapped case | direct | PASS |
| {asymm,un,minlib} | `case_11100` | `case_111100` | SAT | SAT | `comparison.json` mapped case | direct | PASS |
| {asymm,un,no_cycle4} | `case_11001` | `case_110001` | SAT | SAT | `comparison.json` mapped case | direct | PASS |
| {asymm,minlib,no_cycle4} | `case_10101` | `case_101101` | SAT | SAT | `comparison.json` mapped case | direct | PASS |
| {un,minlib,no_cycle4} | `case_01101` | `case_011101` | SAT | SAT | `comparison.json` mapped case | direct | PASS |
| {asymm,un,minlib,no_cycle4} | `case_11101` | `case_111101` | UNSAT | UNSAT | `comparison.json` mapped case | direct | PASS |

**Residual faithfulness verdict: PASS.**

- All 16 entries are directly recorded in the mapped comparison.
- No status comparison required inference.
- Every row applies the `no_cycle3 = off` filter consistently.
- The mapped artifact also records `status_equal: true` per row and
  `mapped_status_equal: true` globally.

Thus `ResidualFaithfulness(E_s, C_b)` is established for the artifact-defined
contract.

## 5. PsiDeletionMonotonicity Justification

The complete `no_cycle3 = 0` bundled contract lattice is present in Section 4.
Its direct artifact statuses are:

- the fully active set `I`, `case_11101`, is UNSAT;
- every one of its 15 proper subsets is SAT.

It follows that for all `T' subseteq T subseteq I`:

```text
SAT(Psi_b(T)) implies SAT(Psi_b(T')).
```

If the antecedent is true, `T` is one of the 15 proper subsets and every
subset `T'` is also among those directly recorded SAT rows. If `T = I`, the
antecedent is false.

**Verdict: PASS, inferred from the complete direct 16-row bundled status
lattice in `comparison.json`.**

This establishes monotonicity of `Psi_b`; it does not assume or claim
deletion-monotonicity of `phi_s`.

## 6. RawRep Completeness Audit

The residual case identifiers below are obtained by deleting the named lever
from fully active split `case_111101`. Each SAT status is direct in
`split/atlas.json` and the corresponding case summary. Membership in
`split_min_repairs` is an enumerator-verified repair record in
`comparison.json`.

| Split singleton deletion R | Split residual status | Evidence source | Classification | Result |
| --- | --- | --- | --- | --- |
| {asymm} | SAT (`case_011101`) | `comparison.json` `split_min_repairs`; `split/atlas.json`; `split/case_011101/summary.json` | direct (via enumeration record) | PASS |
| {un} | SAT (`case_101101`) | `comparison.json` `split_min_repairs`; `split/atlas.json`; `split/case_101101/summary.json` | direct (via enumeration record) | PASS |
| {decisive_voter0} | SAT (`case_110101`) | `comparison.json` `split_min_repairs`; `split/atlas.json`; `split/case_110101/summary.json` | direct (via enumeration record) | PASS |
| {decisive_voter1} | SAT (`case_111001`) | `comparison.json` `split_min_repairs`; `split/atlas.json`; `split/case_111001/summary.json` | direct (via enumeration record) | PASS |
| {no_cycle4} | SAT (`case_111100`) | `comparison.json` `split_min_repairs`; `split/atlas.json`; `split/case_111100/summary.json` | direct (via enumeration record) | PASS |

- Fully active split `case_111101` is directly recorded UNSAT.
- All five singleton deletions are directly recorded SAT.
- `comparison.json` and `split/atlas.json` confirm that the declared
  `Lambda_I` has exactly these five active levers when `no_cycle3` is off.
- Every nonempty deletion of size greater than one properly contains one of
  the five singleton repairs and therefore cannot be inclusion-minimal.

By singleton dominance:

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

**RawRep completeness verdict: PASS, inferred by singleton dominance from
direct enumeration and status records.**

## 7. GroupSoundness Audit via Audit-Cost Collapse

For each raw repair, the bundled residual status is direct in the corresponding
Section 4 mapped row. The `Cross-check` column also uses the
`bundled_min_repairs` enumeration record for fully active bundled
`case_11101`.

| Split raw repair R | group_s(R) | Bundled residual I \ group_s(R) | Required bundled status | Artifact source | Direct or inferred | Cross-check | Result |
| --- | --- | --- | --- | --- | --- | --- | --- |
| {asymm} | {asymm} | {un,minlib,no_cycle4} (`case_01101`) | SAT | `comparison.json` mapped case | direct | Section 4 PASS; `asymm` in `bundled_min_repairs` (direct via enumeration record) | PASS |
| {un} | {un} | {asymm,minlib,no_cycle4} (`case_10101`) | SAT | `comparison.json` mapped case | direct | Section 4 PASS; `un` in `bundled_min_repairs` (direct via enumeration record) | PASS |
| {decisive_voter0} | {minlib} | {asymm,un,no_cycle4} (`case_11001`) | SAT | `comparison.json` mapped case | direct | Section 4 PASS; `minlib` in `bundled_min_repairs` (direct via enumeration record) | PASS |
| {decisive_voter1} | {minlib} | {asymm,un,no_cycle4} (`case_11001`) | SAT | `comparison.json` mapped case | direct | Section 4 PASS; `minlib` in `bundled_min_repairs` (direct via enumeration record) | PASS |
| {no_cycle4} | {no_cycle4} | {asymm,un,minlib} (`case_11100`) | SAT | `comparison.json` mapped case | direct | Section 4 PASS; `no_cycle4` in `bundled_min_repairs` (direct via enumeration record) | PASS |

There is no inconsistency among the Section 7 statuses, the corresponding
Section 4 rows, and `bundled_min_repairs`.

The audit-cost collapse lemma applies because:

1. `PsiDeletionMonotonicity(C_b)` passes;
2. `RawRep(E_s)` is completely identified;
3. all five grouped raw repairs map to directly recorded bundled SAT
   residuals.

Therefore unrestricted `GroupSoundness(E_s, C_b)` is established by inference
from the direct artifact records.

**GroupSoundness verdict: PASS.**

## 8. Audit Verdict Checklist

| Condition | Result | Evidence |
| --- | --- | --- |
| Fully active bundled and split residuals are UNSAT | PASS | `comparison.json`; both atlas files; both fully active case summaries |
| Implementation-deletion-closure is recorded for the split interface | PASS | `split/atlas.json` contains all 64 six-lever subsets, including all 32 `no_cycle3 = 0` five-interface subsets |
| Five singleton repairs are SAT and RawRep completeness follows | PASS | `comparison.json` `split_min_repairs`; five split case summaries; singleton-dominance inference |
| Five grouped reports map to bundled SAT residuals | PASS | Five direct mapped rows in `comparison.json`, cross-checked with `bundled_min_repairs` |
| Sixteen block-aligned residual comparisons match with no_cycle3 off | PASS | 16 direct `comparison.json` mapped rows |
| PsiDeletionMonotonicity is justified | PASS | Inferred from the complete direct 16-row bundled status lattice |
| No new solver run was required | PASS | Artifact-only inspection in this audit |

Overall verdict:

```text
PASS: Candidate B instantiates M3-B under the bundled-level artifact-defined contract.
```

## 9. Interpretation

The Candidate B witness simultaneously supports M1.5 raw-level
non-canonicity and M3-B contract-level grouped report correctness.

Raw repairs are non-canonical across bundled and split implementations, but
under the bundled-level artifact-defined contract `C_b`, verified residual
faithfulness, verified GroupSoundness, and touch-any grouping, the grouped
repair report is canonical:

```text
{
  {asymm},
  {un},
  {minlib},
  {no_cycle4}
}.
```

This does not erase or invalidate M1.5. The result refines it by separating
raw-level non-canonicity from contract-level reportability in the declared
artifact scope.

## 10. Acceptance Criteria

- Exactly one file was created:
  `docs/m3_candidate_b_group_soundness_audit_result.md`.
- No code was modified.
- No solver was run.
- No experimental artifact was created.
- Only existing Candidate B artifacts were used as evidence.
- Every cited status has an artifact source path or a defined path alias from
  Section 2.
- The case bit-order convention is recorded before the status tables.
- The `no_cycle3 = off` filter is applied to all 16 faithfulness rows.
- Evidence classifications follow the declared rule.
- Section 7 rows are cross-checked against Section 4 and
  `bundled_min_repairs`.
- The overall verdict is PASS.
