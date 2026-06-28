# M4 Repair-Orbit and Report-Fiber Precheck Result

## 1. Executive Verdict

1. Group action well-definedness: `PASS`.
   For all `276` repair objects and all `48` elements of
   `S2_voters x S4_alternatives`, the image witness is one of the 36 witness
   configurations and the image repair is in the semantic MCS family for that
   image witness. O2/O3/O4 shape is preserved.

2. Grouped-report map definition: `PASS`.
   The grouped-report map was fixed before this run:

```text
q_atom(asymm) = asymm
q_atom(un) = un
q_atom(no_cycle3) = no_cycle3
q_atom(no_cycle4) = no_cycle4
q_atom(right(voter,P)) = minlib
```

   For repair objects, the primary report key is:

```text
q(target_case, W, R) = (target_case, overlap_class(W), q(R))
```

   The script checked `q(g.x) = q(x)` for all `13248` object/action pairs.
   Result: `q` is `G`-invariant.

3. Report-fiber counts and formal `mu`: `PASS`.
   Formal Phase 2 multiplicity is:

```text
mu(target_case, shape, report) =
  | Fiber(target_case, shape, report) |
```

   This is not the Phase 1 provisional voter-indexed semantic repair
   multiplicity. Phase 1 did not define formal report-fiber `mu`.

4. Repair-orbit/stabilizer computation: `PASS`.
   The run found `16` repair orbits. For every repair object:

```text
|Orb_G(x)| * |Stab_G(x)| = 48
```

5. Fiber-orbit decomposition: `PASS`.
   Every one of the `16` shape-indexed grouped-report fibers is a single
   complete repair orbit. No fiber is a multi-orbit union, and no fiber contains
   partial orbit fragments.

6. O2/O3/O4 dependence: `PASS`.
   The normalized fiber/orbit signatures differ across O2/O3/O4 for both
   target cases. The comparison uses report labels, orbit-size multisets,
   stabilizer-size multisets, orbit counts per report, and partial-fragment
   counts; it is not based on aggregate totals alone.

7. Final verdict:

```text
STRONG GO TO PHASE 3 DESIGN
```

8. Next authorized action:

```text
Write a theoretical design document for Obstruction-Indexed Repair-Orbit
Classification before any theorem implementation.
```

No Lean formalization, no 3-voter run, no warrant-contract work, and no paper
claim promotion are authorized by this Phase 2 result.

## 2. Provenance and Phase 1 Validation

Phase 2 reused the existing Phase 1 temporary output:

```text
/tmp/sen_m4_semantic_mus/precheck_results.json
```

Phase 2 temporary outputs:

```text
/tmp/sen_m4_repair_orbit/repair_orbit_precheck_results.json
/tmp/sen_m4_repair_orbit/object_counts.csv
/tmp/sen_m4_repair_orbit/report_fibers.csv
/tmp/sen_m4_repair_orbit/repair_orbits.csv
/tmp/sen_m4_repair_orbit/shape_comparison.csv
```

Phase 1 scientific-count validation:

| Check | Expected | Observed | Result |
| --- | ---: | ---: | --- |
| Subset statuses | 3456 | 3456 | `PASS` |
| UNKNOWN statuses | 0 | 0 | `PASS` |
| Semantic MUS total | 96 | 96 | `PASS` |
| Semantic MCS total | 276 | 276 | `PASS` |
| MUS/MCS duality | PASS | PASS | `PASS` |
| O2/O3/O4 shape verdict | PASS | PASS | `PASS` |
| Voter-swap equivariance | PASS | PASS | `PASS` |

## 3. Repair Object and Group

The computed repair object is:

```text
RepairObject := (target_case, W, R)
```

where `target_case in {case_11101, case_11111}`,
`W = ((voter0,P),(voter1,Q))`, and `R` is a semantic MCS for the
selector-free fixed-witness theory associated with `W`.

`R` alone is not a repair object in this analysis. The witness configuration
`W` is part of object identity.

The group is:

```text
G = S2_voters x S4_alternatives
|G| = 48
```

Target cases are fixed by the action; no orbit crosses from `case_11101` to
`case_11111`.

## 4. Object Counts

| Target | Shape | Witness configurations | MCS count | Repair objects | Reports | Fibers | Orbits |
| --- | --- | ---: | ---: | ---: | ---: | ---: | ---: |
| `case_11101` | O2 | 6 | 18 | 18 | 2 | 2 | 2 |
| `case_11101` | O3 | 24 | 96 | 96 | 3 | 3 | 3 |
| `case_11101` | O4 | 6 | 24 | 24 | 3 | 3 | 3 |
| `case_11111` | O2 | 6 | 18 | 18 | 2 | 2 | 2 |
| `case_11111` | O3 | 24 | 96 | 96 | 3 | 3 | 3 |
| `case_11111` | O4 | 6 | 24 | 24 | 3 | 3 | 3 |

Totals:

| Item | Count |
| --- | ---: |
| Repair objects | 276 |
| Shape-indexed report fibers | 16 |
| Repair orbits | 16 |
| Partial orbit fragments | 0 |

## 5. Report-Fiber Table

Each row fixes `(target_case, shape, report)`. `mu` is the fiber cardinality.

| Target | Shape | Report | `mu` | Orbits in fiber | Orbit sizes inside fiber | Stabilizer-size multiset | Single orbit? | Stable complete orbit union? | Partial fragments? | Representative repair object |
| --- | --- | --- | ---: | ---: | --- | --- | --- | --- | --- | --- |
| `case_11101` | O2 | `{asymm}` | 6 | 1 | `[6]` | `[8]` | `true` | `true` | `false` | `W=((voter0,{0,1}),(voter1,{0,1})), R={asymm}` |
| `case_11101` | O2 | `{minlib}` | 12 | 1 | `[12]` | `[4]` | `true` | `true` | `false` | `W=((voter0,{0,1}),(voter1,{0,1})), R={right(voter0,{0,1})}` |
| `case_11101` | O3 | `{un}` | 24 | 1 | `[24]` | `[2]` | `true` | `true` | `false` | `W=((voter0,{0,1}),(voter1,{0,2})), R={un}` |
| `case_11101` | O3 | `{minlib}` | 48 | 1 | `[48]` | `[1]` | `true` | `true` | `false` | `W=((voter0,{0,1}),(voter1,{0,2})), R={right(voter0,{0,1})}` |
| `case_11101` | O3 | `{no_cycle4}` | 24 | 1 | `[24]` | `[2]` | `true` | `true` | `false` | `W=((voter0,{0,1}),(voter1,{0,2})), R={no_cycle4}` |
| `case_11101` | O4 | `{un}` | 6 | 1 | `[6]` | `[8]` | `true` | `true` | `false` | `W=((voter0,{0,1}),(voter1,{2,3})), R={un}` |
| `case_11101` | O4 | `{minlib}` | 12 | 1 | `[12]` | `[4]` | `true` | `true` | `false` | `W=((voter0,{0,1}),(voter1,{2,3})), R={right(voter0,{0,1})}` |
| `case_11101` | O4 | `{no_cycle4}` | 6 | 1 | `[6]` | `[8]` | `true` | `true` | `false` | `W=((voter0,{0,1}),(voter1,{2,3})), R={no_cycle4}` |
| `case_11111` | O2 | `{asymm}` | 6 | 1 | `[6]` | `[8]` | `true` | `true` | `false` | `W=((voter0,{0,1}),(voter1,{0,1})), R={asymm}` |
| `case_11111` | O2 | `{minlib}` | 12 | 1 | `[12]` | `[4]` | `true` | `true` | `false` | `W=((voter0,{0,1}),(voter1,{0,1})), R={right(voter0,{0,1})}` |
| `case_11111` | O3 | `{un}` | 24 | 1 | `[24]` | `[2]` | `true` | `true` | `false` | `W=((voter0,{0,1}),(voter1,{0,2})), R={un}` |
| `case_11111` | O3 | `{minlib}` | 48 | 1 | `[48]` | `[1]` | `true` | `true` | `false` | `W=((voter0,{0,1}),(voter1,{0,2})), R={right(voter0,{0,1})}` |
| `case_11111` | O3 | `{no_cycle3, no_cycle4}` | 24 | 1 | `[24]` | `[2]` | `true` | `true` | `false` | `W=((voter0,{0,1}),(voter1,{0,2})), R={no_cycle3, no_cycle4}` |
| `case_11111` | O4 | `{un}` | 6 | 1 | `[6]` | `[8]` | `true` | `true` | `false` | `W=((voter0,{0,1}),(voter1,{2,3})), R={un}` |
| `case_11111` | O4 | `{minlib}` | 12 | 1 | `[12]` | `[4]` | `true` | `true` | `false` | `W=((voter0,{0,1}),(voter1,{2,3})), R={right(voter0,{0,1})}` |
| `case_11111` | O4 | `{no_cycle4}` | 6 | 1 | `[6]` | `[8]` | `true` | `true` | `false` | `W=((voter0,{0,1}),(voter1,{2,3})), R={no_cycle4}` |

Interpretation discipline: because each fiber is a single orbit, the grouped
report identifies a repair orbit. It does not identify a raw repair object
without quotienting by the group action.

## 6. Orbit Table

The notation `id:0123` means identity voter action and alternative permutation
`0->0, 1->1, 2->2, 3->3`. The notation `tau:0213` means voter swap and
alternative permutation `0->0, 1->2, 2->1, 3->3`.

| Orbit | Target | Shape | Representative `W` | Representative `R` | `q(R)` | Orbit size | Stabilizer size | Stabilizer generators | Stabilizer elements | Reports in orbit | One report fiber? |
| --- | --- | --- | --- | --- | --- | ---: | ---: | --- | --- | --- | --- |
| `orbit_000` | `case_11101` | O2 | `((voter0,{0,1}),(voter1,{0,1}))` | `{asymm}` | `{asymm}` | 6 | 8 | `id:0132`, `id:1023`, `tau:0123` | `id:0123`, `id:0132`, `id:1023`, `id:1032`, `tau:0123`, `tau:0132`, `tau:1023`, `tau:1032` | `{asymm}` | `true` |
| `orbit_001` | `case_11101` | O2 | `((voter0,{0,1}),(voter1,{0,1}))` | `{right(voter0,{0,1})}` | `{minlib}` | 12 | 4 | `id:0132`, `id:1023` | `id:0123`, `id:0132`, `id:1023`, `id:1032` | `{minlib}` | `true` |
| `orbit_002` | `case_11101` | O3 | `((voter0,{0,1}),(voter1,{0,2}))` | `{un}` | `{un}` | 24 | 2 | `tau:0213` | `id:0123`, `tau:0213` | `{un}` | `true` |
| `orbit_003` | `case_11101` | O3 | `((voter0,{0,1}),(voter1,{0,2}))` | `{no_cycle4}` | `{no_cycle4}` | 24 | 2 | `tau:0213` | `id:0123`, `tau:0213` | `{no_cycle4}` | `true` |
| `orbit_004` | `case_11101` | O3 | `((voter0,{0,1}),(voter1,{0,2}))` | `{right(voter0,{0,1})}` | `{minlib}` | 48 | 1 | empty | `id:0123` | `{minlib}` | `true` |
| `orbit_005` | `case_11101` | O4 | `((voter0,{0,1}),(voter1,{2,3}))` | `{un}` | `{un}` | 6 | 8 | `id:0132`, `id:1023`, `tau:2301` | `id:0123`, `id:0132`, `id:1023`, `id:1032`, `tau:2301`, `tau:2310`, `tau:3201`, `tau:3210` | `{un}` | `true` |
| `orbit_006` | `case_11101` | O4 | `((voter0,{0,1}),(voter1,{2,3}))` | `{no_cycle4}` | `{no_cycle4}` | 6 | 8 | `id:0132`, `id:1023`, `tau:2301` | `id:0123`, `id:0132`, `id:1023`, `id:1032`, `tau:2301`, `tau:2310`, `tau:3201`, `tau:3210` | `{no_cycle4}` | `true` |
| `orbit_007` | `case_11101` | O4 | `((voter0,{0,1}),(voter1,{2,3}))` | `{right(voter0,{0,1})}` | `{minlib}` | 12 | 4 | `id:0132`, `id:1023` | `id:0123`, `id:0132`, `id:1023`, `id:1032` | `{minlib}` | `true` |
| `orbit_008` | `case_11111` | O2 | `((voter0,{0,1}),(voter1,{0,1}))` | `{asymm}` | `{asymm}` | 6 | 8 | `id:0132`, `id:1023`, `tau:0123` | `id:0123`, `id:0132`, `id:1023`, `id:1032`, `tau:0123`, `tau:0132`, `tau:1023`, `tau:1032` | `{asymm}` | `true` |
| `orbit_009` | `case_11111` | O2 | `((voter0,{0,1}),(voter1,{0,1}))` | `{right(voter0,{0,1})}` | `{minlib}` | 12 | 4 | `id:0132`, `id:1023` | `id:0123`, `id:0132`, `id:1023`, `id:1032` | `{minlib}` | `true` |
| `orbit_010` | `case_11111` | O3 | `((voter0,{0,1}),(voter1,{0,2}))` | `{un}` | `{un}` | 24 | 2 | `tau:0213` | `id:0123`, `tau:0213` | `{un}` | `true` |
| `orbit_011` | `case_11111` | O3 | `((voter0,{0,1}),(voter1,{0,2}))` | `{right(voter0,{0,1})}` | `{minlib}` | 48 | 1 | empty | `id:0123` | `{minlib}` | `true` |
| `orbit_012` | `case_11111` | O3 | `((voter0,{0,1}),(voter1,{0,2}))` | `{no_cycle3, no_cycle4}` | `{no_cycle3, no_cycle4}` | 24 | 2 | `tau:0213` | `id:0123`, `tau:0213` | `{no_cycle3, no_cycle4}` | `true` |
| `orbit_013` | `case_11111` | O4 | `((voter0,{0,1}),(voter1,{2,3}))` | `{un}` | `{un}` | 6 | 8 | `id:0132`, `id:1023`, `tau:2301` | `id:0123`, `id:0132`, `id:1023`, `id:1032`, `tau:2301`, `tau:2310`, `tau:3201`, `tau:3210` | `{un}` | `true` |
| `orbit_014` | `case_11111` | O4 | `((voter0,{0,1}),(voter1,{2,3}))` | `{no_cycle4}` | `{no_cycle4}` | 6 | 8 | `id:0132`, `id:1023`, `tau:2301` | `id:0123`, `id:0132`, `id:1023`, `id:1032`, `tau:2301`, `tau:2310`, `tau:3201`, `tau:3210` | `{no_cycle4}` | `true` |
| `orbit_015` | `case_11111` | O4 | `((voter0,{0,1}),(voter1,{2,3}))` | `{right(voter0,{0,1})}` | `{minlib}` | 12 | 4 | `id:0132`, `id:1023` | `id:0123`, `id:0132`, `id:1023`, `id:1032` | `{minlib}` | `true` |

Every listed orbit is shape-preserving, report-preserving, and target-case
preserving.

## 7. Shape Comparison

The shape signatures below use:

- fiber-size by report;
- orbit-size multiset;
- number of orbits per report;
- single-orbit and multi-orbit fiber counts;
- partial-orbit-fragment count;
- stabilizer-size multiset;
- report labels present.

| Target | Shape | Fiber size by report | Orbit sizes | Orbits per report | Single-orbit fibers | Multi-orbit fibers | Partial fragments | Stabilizer sizes | Report labels |
| --- | --- | --- | --- | --- | ---: | ---: | ---: | --- | --- |
| `case_11101` | O2 | `{asymm}:6, {minlib}:12` | `[6,12]` | all `1` | 2 | 0 | 0 | `[4,8]` | `{asymm}`, `{minlib}` |
| `case_11101` | O3 | `{un}:24, {minlib}:48, {no_cycle4}:24` | `[24,24,48]` | all `1` | 3 | 0 | 0 | `[1,2,2]` | `{un}`, `{minlib}`, `{no_cycle4}` |
| `case_11101` | O4 | `{un}:6, {minlib}:12, {no_cycle4}:6` | `[6,6,12]` | all `1` | 3 | 0 | 0 | `[4,8,8]` | `{un}`, `{minlib}`, `{no_cycle4}` |
| `case_11111` | O2 | `{asymm}:6, {minlib}:12` | `[6,12]` | all `1` | 2 | 0 | 0 | `[4,8]` | `{asymm}`, `{minlib}` |
| `case_11111` | O3 | `{un}:24, {minlib}:48, {no_cycle3, no_cycle4}:24` | `[24,24,48]` | all `1` | 3 | 0 | 0 | `[1,2,2]` | `{un}`, `{minlib}`, `{no_cycle3, no_cycle4}` |
| `case_11111` | O4 | `{un}:6, {minlib}:12, {no_cycle4}:6` | `[6,6,12]` | all `1` | 3 | 0 | 0 | `[4,8,8]` | `{un}`, `{minlib}`, `{no_cycle4}` |

Shape-dependence verdict:

- `case_11101`: O2 differs from O3/O4 by report labels and stabilizer/orbit
  profile. O3 and O4 have the same report labels but differ in orbit sizes and
  stabilizer-size multiset under the full `S2 x S4` action.
- `case_11111`: O2, O3, and O4 are all separated by report labels and/or
  orbit-stabilizer signatures. O3 has the distinctive report
  `{no_cycle3, no_cycle4}`.
- No partial-orbit fragment exists in any shape. Thus no observed fiber cuts
  across a repair orbit.

## 8. Interpretation

The grouped report is `G`-invariant. In this two-voter Sen24 setting, each
shape-indexed grouped-report fiber is exactly one repair orbit.

Therefore, the grouped report identifies a repair orbit, not a raw repair
object. This is a quotient-level identifiability result for the precheck.

The result is stronger than a bare voter-swap duplication: alternative
relabeling participates in all orbit computations, and O2/O3/O4 differ in
orbit sizes, stabilizer sizes, and report labels.

## 9. Validation

Commands run:

```bash
PYTHONPYCACHEPREFIX=/tmp/sen_m4_repair_orbit/pycache \
python3 -m py_compile \
  scripts/exploration/m4/repair_orbit_precheck.py \
  scripts/exploration/m4/test_repair_orbit_precheck.py
```

Result: `PASS`.

```bash
PYTHONPYCACHEPREFIX=/tmp/sen_m4_repair_orbit/pycache \
python3 scripts/exploration/m4/test_repair_orbit_precheck.py
```

Result: `PASS` (`13` tests).

```bash
PYTHONPYCACHEPREFIX=/tmp/sen_m4_repair_orbit/pycache \
python3 scripts/exploration/m4/repair_orbit_precheck.py \
  --out-dir /tmp/sen_m4_repair_orbit
```

Result:

```text
group_size = 48
phase1_source_mode = reused
repair_object_count = 276
report_fiber_count = 16
repair_orbit_count = 16
well_definedness = true
q_invariance = true
verdict = STRONG GO TO PHASE 3 DESIGN
```

## 10. Scope and Non-Claims

Only the Phase 2 plan, result, exploratory script, and focused test file are
changed by this task.

This Phase 2 result does not claim:

- Lean theorem;
- M4 final theorem;
- 3-voter result;
- Arrow result;
- Gibbard-Satterthwaite result;
- general social-choice theorem;
- warrant-contract semantics;
- Delegated Warrant Preservation theorem;
- paper-ready claim;
- semantic-to-CNF correctness theorem.
