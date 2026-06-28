# M4 Repair-Orbit and Report-Fiber Precheck Plan

## 1. Purpose

This Phase 2 precheck tests whether the selector-free semantic MUS/MCS
obstruction-shape geometry from Phase 1 explains semantic repair objects under
the natural voter and alternative relabeling action.

The core question is:

```text
For each target residual and O2/O3/O4 obstruction shape, does the
grouped-report fiber q^{-1}(p) decompose into natural repair orbits under
voter/alternative relabeling?
```

This is not an M4 theorem implementation. It does not authorize Lean
formalization, a 3-voter extension, warrant-contract semantics, or paper-claim
promotion.

## 2. Phase 1 Inputs

The input is the selector-free semantic MUS/MCS output from Phase 1 for:

```text
case_11101
case_11111
```

Phase 2 must validate the Phase 1 scientific counts before computing repair
orbits:

| Check | Expected |
| --- | ---: |
| Subset statuses | 3456 |
| UNKNOWN statuses | 0 |
| Semantic MUS total | 96 |
| Semantic MCS total | 276 |
| MUS/MCS duality | PASS |
| O2/O3/O4 shape verdict | PASS |
| Voter-swap equivariance | PASS |

Temporary Phase 1 outputs may be reused from `/tmp/sen_m4_semantic_mus/` or
regenerated if missing. They are not promoted to tracked results.

## 3. Repair Object

Phase 2 uses the repair object:

```text
RepairObject := (target_case, W, R)
```

where:

```text
target_case in {case_11101, case_11111}

W = ((voter0, P), (voter1, Q))
```

and `P,Q` are unordered alternative pairs over `{0,1,2,3}`.

`R` is a semantic MCS for the selector-free fixed-witness theory associated
with `W`.

The repair object is not just `R`. The witness configuration `W` remains part
of the object so equal-looking MCS labels from different witness configurations
are not identified.

Semantic atoms are:

```text
asymm
un
no_cycle3
no_cycle4
right(voter, unordered_alt_pair)
```

## 4. Group Action

The finite group is:

```text
G = S2_voters x S4_alternatives
|G| = 2 * 24 = 48
```

The target case is fixed by the action. Phase 2 does not form orbits across
`case_11101` and `case_11111`.

For the voter swap `tau`:

```text
tau(((voter0,P),(voter1,Q))) = ((voter0,Q),(voter1,P))
tau(right(voter0,P)) = right(voter1,P)
tau(right(voter1,Q)) = right(voter0,Q)
tau(base_atom) = base_atom
```

For an alternative permutation `sigma in S4`:

```text
sigma({a,b}) = canonical_unordered_pair({sigma(a), sigma(b)})
sigma(right(voter,{a,b})) = right(voter, sigma({a,b}))
sigma(base_atom) = base_atom
```

The product action is:

```text
g . (target_case, W, R) = (target_case, gW, gR)
```

## 5. Well-Definedness Checks

Before orbit analysis, the script must verify:

1. `gW` is one of the 36 witness configurations.
2. `gR` is in the semantic MCS family for `gW`.
3. Both checks hold for every repair object and every `g in G`.
4. O2/O3/O4 shape is preserved.

If any check fails, Phase 2 cannot receive a GO verdict. The counterexamples
must be recorded in the result payload.

## 6. Grouped-Report Map

The grouped-report map is fixed before inspecting Phase 2 results:

```text
q_atom(asymm) = asymm
q_atom(un) = un
q_atom(no_cycle3) = no_cycle3
q_atom(no_cycle4) = no_cycle4
q_atom(right(voter,P)) = minlib
```

For a semantic repair set:

```text
q(R) = sorted set { q_atom(a) | a in R }
```

For a repair object:

```text
q(target_case, W, R) = (target_case, overlap_class(W), q(R))
```

The primary fibers fix target case and O2/O3/O4 shape:

```text
Fiber(target_case, shape, report) =
  { (target_case, W, R)
    | overlap_class(W)=shape
      and R is semantic MCS for W
      and q(R)=report }
```

The script must verify:

```text
q(g.x) = q(x)
```

for all repair objects and all `g in G`.

## 7. Formal Mu

Phase 2 defines formal report-fiber multiplicity as:

```text
mu(target_case, shape, report) :=
  | Fiber(target_case, shape, report) |
```

This is distinct from Phase 1's provisional voter-indexed semantic repair
multiplicity. Phase 1 did not define formal report-fiber `mu`.

## 8. Orbit and Stabilizer Computation

For each repair object `x`:

```text
Orb_G(x) = { g.x | g in G }
Stab_G(x) = { g in G | g.x = x }
```

The script checks:

```text
|Orb_G(x)| * |Stab_G(x)| = |G| = 48
```

for every repair object.

For each shape-indexed fiber, the script computes:

```text
OrbitPartition(Fiber) :=
  set of G-orbits intersecting that fiber
```

and records whether the fiber is:

- a single repair orbit;
- a stable union of complete repair orbits;
- cut by partial orbit fragments.

Partial orbit fragments are treated as serious evidence that `q` is not a
well-behaved grouped report for this action.

## 9. Required Outputs

The temporary output directory is:

```text
/tmp/sen_m4_repair_orbit/
```

The script writes:

```text
repair_orbit_precheck_results.json
object_counts.csv
report_fibers.csv
repair_orbits.csv
shape_comparison.csv
```

The tracked result document reports:

- executive verdict;
- object counts;
- report-fiber table;
- orbit table;
- O2/O3/O4 shape comparison;
- non-claims;
- validation commands.

## 10. Verdict Criteria

### STRONG GO TO OBSTRUCTION-INDEXED ORBIT-CLASSIFICATION DESIGN

Renamed after review to avoid confusion with the separate possible three-voter
S3 extension phase.

All must hold:

1. The group action is well-defined on repair objects.
2. `q` is `G`-invariant.
3. Every shape-indexed report fiber is a single repair orbit, or every fiber is
   a stable finite union of complete repair orbits.
4. O2/O3/O4 have representative-level differences in fiber/orbit signatures.
5. No result depends on selector machinery, naming artifacts, or aggregate
   count alone.
6. Formal `mu` is computed and reported.

The next action is a theoretical design document only.

### CONDITIONAL GO

Use when the action, `q`, and fiber decomposition are coherent, but some
O2/O3/O4 signatures coincide or the eventual statement needs case
distinctions.

### WEAK GO / NEEDS 3-VOTER

Use when the two-voter orbit/fiber structure is coherent, but the only
nontriviality is essentially voter-swap symmetry or O2/O3/O4 dependence is
weak.

### NO-GO

Use when the group action is not well-defined, `q` is not invariant, fibers cut
across orbits unstably, formal `mu` depends on representation choices, or the
structure collapses to duplicated rights blocks without obstruction-indexed
content.

## 11. Non-Claims

Phase 2 does not claim:

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
