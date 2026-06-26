# M4 Semantic MUS Symmetry Precheck Result

## 1. Executive Verdict

1. Selector-free phenomenon survival: `PASS`.
   Every selector-free fixed-witness package reproduced the expected `UNSAT`
   status, and voter-indexed semantic repair multiplicity survived.
2. O2/O3/O4 shape-comparison verdict: `PASS`.
   Representative-level `ShapeSignature` values are stable within each
   O2/O3/O4 class under alternative relabeling, and cross-shape structural
   differences are present.
3. Voter-swap equivariance: `PASS`.
   `MUS(tau(W)) = tau(MUS(W))` and `MCS(tau(W)) = tau(MCS(W))` for every
   witness configuration.
4. MUS/MCS duality: `PASS`.
   Directly enumerated MCS equals the minimal hitting-set family of the complete
   MUS family for every configuration.
5. Final gate verdict:

```text
STRONG GO
```

6. Next authorized action:
   create a separate M4 scope-decision document deciding whether semantic MUS
   orbit structure should enter the M4 warrant-contract design.

This is a pre-M4 mathematical gate result. It is not an M4 theorem
implementation, not a Lean formalization, and not a change to the current M4
scope.

## 2. Semantic Atom Definitions

The MUS universe is semantic, not clause-level.

Base atoms:

```text
asymm
un
no_cycle3
no_cycle4
```

Rights atoms:

```text
right(voter, unordered_alt_pair)
```

`right(i,{x,y})` means that voter `i` is decisive for unordered alternative
pair `{x,y}`. Pair orientation is canonicalized by sorting endpoints, so
`{x,y}` and `{y,x}` are the same semantic atom.

For a fixed right `right(i,{x,y})`, the selector-free clause block directly
requires the social comparison over `{x,y}` to follow voter `i` at every Sen24
profile.

Each semantic atom block receives an independent activation guard variable and
a provenance label. Guard variables are not semantic MUS atoms.

## 3. Pre-Registered Shape Signature

The shape comparison used the pre-registered signature:

```text
ShapeSignature(W) :=
  (
    MUS cardinality multiset,
    MCS cardinality multiset,
    rights participation multiset,
    minimal rights-only hitting-set family,
    MUS hypergraph degree sequence,
    voter-swap stabilizer profile,
    repair-orbit size profile
  )
```

The Phase 1 run does not fully define formal report-fiber multiplicity `mu`.
Where the tables below mention `mu`, they report only provisional
voter-indexed semantic repair multiplicity. This is kept distinct from a future
formal report-fiber `mu`.

O2/O3/O4 have different numbers of witness configurations. Aggregate MUS/MCS
totals are therefore reference values only and are not used as evidence for
`STRONG GO`. The decisive comparison is the normalized signature of each
alternative-relabeling orbit representative.

## 4. Witness Configurations and Target Residuals

There are six unordered alternative pairs over alternatives `{0,1,2,3}`:

```text
{0,1}, {0,2}, {0,3}, {1,2}, {1,3}, {2,3}
```

The precheck enumerated all ordered two-voter witness configurations:

```text
((voter0, P), (voter1, Q))
```

Exact witness count:

```text
6 * 6 = 36
```

Each witness was evaluated against both target residuals, for `72`
configuration-result rows.

| Target | Production active levers | Semantic active universe |
| --- | --- | --- |
| `case_11101` | `asymm`, `un`, `minlib`, `no_cycle4` | `asymm`, `un`, `no_cycle4`, `right(voter0,P)`, `right(voter1,Q)` |
| `case_11111` | `asymm`, `un`, `minlib`, `no_cycle3`, `no_cycle4` | `asymm`, `un`, `no_cycle3`, `no_cycle4`, `right(voter0,P)`, `right(voter1,Q)` |

Production bit order:

```text
asymm, un, minlib, no_cycle3, no_cycle4
```

For every witness configuration, the full selector-free semantic package was
`UNSAT` for both target residuals.

## 5. Solver and Command Provenance

Command:

```bash
PYTHONPYCACHEPREFIX=/tmp/sen_m4_semantic_mus/pycache \
  python3 scripts/exploration/m4/semantic_mus_precheck.py \
  --out-dir /tmp/sen_m4_semantic_mus \
  --solver cadical \
  --timeout 20
```

Solver provenance:

| Field | Value |
| --- | --- |
| Solver | `cadical` |
| Solver path | `/opt/homebrew/Cellar/cadical/3.0.0/bin/cadical` |
| Solver version | `3.0.0` |
| Python version | `3.9.6` |
| Platform | `macOS-15.6.1-arm64-arm-64bit` |

Temporary output files:

- `/tmp/sen_m4_semantic_mus/precheck_results.json`
- `/tmp/sen_m4_semantic_mus/configuration_summary.csv`
- `/tmp/sen_m4_semantic_mus/subset_statuses.csv`
- `/tmp/sen_m4_semantic_mus/o2_o3_o4.csv`
- `/tmp/sen_m4_semantic_mus/voter_swap.csv`
- `/tmp/sen_m4_semantic_mus/shape_signatures.csv`

Raw JSON is not copied into the repository. The `/tmp` files are execution
outputs, not canonical tracked results.

## 6. Selector-Free Survival and Complete Enumeration

Every subset of each active semantic atom universe was enumerated.

| Item | Count |
| --- | ---: |
| Witness configurations | 36 |
| Configuration-result rows | 72 |
| Subset statuses | 3456 |
| `UNKNOWN` statuses | 0 |
| Semantic MUS | 96 |
| Semantic MCS | 276 |

Reference aggregate totals by target/class:

| Target | Class | Configs | Subsets | SAT | UNSAT | UNKNOWN | MUS | MCS |
| --- | --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| `case_11101` | O2 | 6 | 192 | 168 | 24 | 0 | 6 | 18 |
| `case_11101` | O3 | 24 | 768 | 720 | 48 | 0 | 24 | 96 |
| `case_11101` | O4 | 6 | 192 | 180 | 12 | 0 | 6 | 24 |
| `case_11111` | O2 | 6 | 384 | 336 | 48 | 0 | 6 | 18 |
| `case_11111` | O3 | 24 | 1536 | 1392 | 144 | 0 | 48 | 96 |
| `case_11111` | O4 | 6 | 384 | 360 | 24 | 0 | 6 | 24 |

These totals are not used as the basis for `STRONG GO`; they are included only
for accounting.

## 7. Shape-Comparison Table: `case_11101`

Canonical representatives:

| Shape | Representative |
| --- | --- |
| O2 | `v0_01__v1_01` |
| O3 | `v0_01__v1_02` |
| O4 | `v0_01__v1_23` |

Here `R0` abbreviates `right(voter0,P)` and `R1` abbreviates
`right(voter1,Q)` for the representative.

| Invariant | O2 | O3 | O4 |
| --- | ---: | ---: | ---: |
| Number of semantic MUS per representative | 1 | 1 | 1 |
| MUS cardinality multiset | `[3]` | `[4]` | `[4]` |
| Number of semantic MCS per representative | 3 | 4 | 4 |
| MCS cardinality multiset | `[1,1,1]` | `[1,1,1,1]` | `[1,1,1,1]` |
| Provisional voter-indexed semantic repair multiplicity, not formal `mu` | 2 | 2 | 2 |
| Rights participation signature | `[[R0,R1]]` | `[[R0,R1]]` | `[[R0,R1]]` |
| Rights-core intersection | `[R0,R1]` | `[R0,R1]` | `[R0,R1]` |
| Minimal rights-only hitting-set family | `[[R0],[R1]]` | `[[R0],[R1]]` | `[[R0],[R1]]` |
| MUS hypergraph degree sequence | `[(R0,1),(R1,1),(asymm,1)]` | `[(R0,1),(R1,1),(no_cycle4,1),(un,1)]` | `[(R0,1),(R1,1),(no_cycle4,1),(un,1)]` |
| Voter-swap stabilizer profile | full `{id,tau}`; proper `{tau}` | full `{id}`; proper empty | full `{id}`; proper empty |
| Repair-orbit size profile | 1 | 2 | 2 |

Within-shape stability:

| Shape | Representative signatures under alternative relabeling | Stable? |
| --- | ---: | --- |
| O2 | 1 | `true` |
| O3 | 1 | `true` |
| O4 | 1 | `true` |

Cross-shape structural difference:

- O2 differs from O3/O4 in MUS cardinality, MCS cardinality, MCS count, and
  degree sequence.
- O3 and O4 coincide for this residual, but STRONG GO does not require every
  pair of shapes to differ. It requires at least one pre-registered structural
  component to distinguish shapes in a representative-level comparison.

## 8. Shape-Comparison Table: `case_11111`

Canonical representatives:

| Shape | Representative |
| --- | --- |
| O2 | `v0_01__v1_01` |
| O3 | `v0_01__v1_02` |
| O4 | `v0_01__v1_23` |

| Invariant | O2 | O3 | O4 |
| --- | ---: | ---: | ---: |
| Number of semantic MUS per representative | 1 | 2 | 1 |
| MUS cardinality multiset | `[3]` | `[4,4]` | `[4]` |
| Number of semantic MCS per representative | 3 | 4 | 4 |
| MCS cardinality multiset | `[1,1,1]` | `[1,1,1,2]` | `[1,1,1,1]` |
| Provisional voter-indexed semantic repair multiplicity, not formal `mu` | 2 | 2 | 2 |
| Rights participation signature | `[[R0,R1]]` | `[[R0,R1],[R0,R1]]` | `[[R0,R1]]` |
| Rights-core intersection | `[R0,R1]` | `[R0,R1]` | `[R0,R1]` |
| Minimal rights-only hitting-set family | `[[R0],[R1]]` | `[[R0],[R1]]` | `[[R0],[R1]]` |
| MUS hypergraph degree sequence | `[(R0,1),(R1,1),(asymm,1)]` | `[(no_cycle3,1),(no_cycle4,1),(R0,2),(R1,2),(un,2)]` | `[(R0,1),(R1,1),(no_cycle4,1),(un,1)]` |
| Voter-swap stabilizer profile | full `{id,tau}`; proper `{tau}` | full `{id}`; proper empty | full `{id}`; proper empty |
| Repair-orbit size profile | 1 | 2 | 2 |

Within-shape stability:

| Shape | Representative signatures under alternative relabeling | Stable? |
| --- | ---: | --- |
| O2 | 1 | `true` |
| O3 | 1 | `true` |
| O4 | 1 | `true` |

Cross-shape structural difference:

- O2, O3, and O4 have three distinct structural signature forms.
- O3 is separated by two MUS of cardinality four, the MCS cardinality multiset
  `[1,1,1,2]`, and degree sequence entries of degree two for `R0`, `R1`, and
  `un`.
- The difference is representative-level and normalized; it is not an artifact
  of witness-count totals.

## 9. MUS/MCS Class Forms

The following representative forms explain the tables above.

| Target | Class | Representative MUS form | Representative MCS form |
| --- | --- | --- | --- |
| `case_11101` | O2 | `{asymm, R0, R1}` | `{asymm}`, `{R0}`, `{R1}` |
| `case_11101` | O3 | `{un, no_cycle4, R0, R1}` | `{un}`, `{no_cycle4}`, `{R0}`, `{R1}` |
| `case_11101` | O4 | `{un, no_cycle4, R0, R1}` | `{un}`, `{no_cycle4}`, `{R0}`, `{R1}` |
| `case_11111` | O2 | `{asymm, R0, R1}` | `{asymm}`, `{R0}`, `{R1}` |
| `case_11111` | O3 | `{un, no_cycle3, R0, R1}` and `{un, no_cycle4, R0, R1}` | `{un}`, `{R0}`, `{R1}`, `{no_cycle3, no_cycle4}` |
| `case_11111` | O4 | `{un, no_cycle4, R0, R1}` | `{un}`, `{no_cycle4}`, `{R0}`, `{R1}` |

For every configuration, directly enumerated MCS equals the minimal hitting
sets of the complete MUS family.

## 10. Rights Participation Metrics

Every MUS contains both fixed rights atoms. No rights-free MUS was found.

| Metric | Result |
| --- | --- |
| Any MUS contains neither right | `false` |
| Every MUS contains both rights | `true` |
| Rights intersection across all MUS | both `R0` and `R1` |
| Minimal rights-only hitting sets | `{R0}` and `{R1}` |
| Only one voter's right present in every MUS | `false` |
| Singleton right MCS for voter0 | present in every configuration |
| Singleton right MCS for voter1 | present in every configuration |
| Semantic voter-indexed repair multiplicity survives | `true` |

This is the selector-contamination check: the multiplicity persists when the
selector implementation is removed and rights are fixed semantic atoms.

## 11. Voter-Swap Equivariance

The voter swap `tau` exchanges voter `0` and voter `1`.

For every witness configuration `W`:

```text
MUS(tau(W)) = tau(MUS(W))
MCS(tau(W)) = tau(MCS(W))
```

Result:

| Check | Result |
| --- | --- |
| MUS voter-swap equivariance | `true` for all 72 configuration-result rows |
| MCS voter-swap equivariance | `true` for all 72 configuration-result rows |

Stabilizer/orbit distinction:

| Configuration type | Full stabilizer | Proper stabilizer | Orbit size |
| --- | --- | --- | --- |
| O2 with `P = Q` | `{id, tau}` | `{tau}` | 1 |
| O3/O4 with `P != Q` | `{id}` | empty | 2 |

Voter-swap equivariance alone would only show that the construction respects
voter symmetry. It is not by itself evidence of O2/O3/O4 shape dependence.

## 12. Selector-Contamination Exclusion

The exploratory fixed-witness encoder did not use:

- `sel0`;
- `sel1`;
- voter-pair selector variables;
- role-specific selector variables;
- selector-existence clauses.

The only variables above the Sen24 profile/pair variables are independent
activation guards for semantic atom blocks. Those guards are not part of the
semantic MUS universe.

Therefore the observed voter-indexed repair multiplicity is not created by the
legacy selector clauses.

## 13. Strengthened Gate Evaluation

| STRONG GO criterion | Result |
| --- | --- |
| Selector-free fixed-witness theory preserves semantic repair multiplicity | `PASS` |
| Complete MUS/MCS duality holds | `PASS` |
| Voter-swap equivariance holds | `PASS` |
| Same-shape representative signatures are stable under alternative relabeling | `PASS` |
| At least one pre-registered `ShapeSignature` component differs across O2/O3/O4 | `PASS` |
| Difference is not configuration count, naming, selector machinery, or aggregate total | `PASS` |
| No `UNKNOWN` status blocks classification | `PASS` |

Final gate verdict:

```text
STRONG GO
```

Interpretation:

- `mu` being shape-dependent would be a sufficient evidence candidate for
  STRONG GO, but it is not required.
- Here the provisional voter-indexed semantic repair multiplicity is constant
  at `2`, so STRONG GO is supported by other pre-registered invariants:
  MUS cardinality, MCS cardinality, representative MUS count, and hypergraph
  degree sequence.
- A `mu` difference alone would not justify STRONG GO unless it were a
  normalized representative-level difference.
- Same-shape stability and cross-shape structural difference are both present.

## 14. Next Action

Create a separate M4 scope-decision document deciding whether and how semantic
MUS orbit structure should enter the M4 warrant-contract design.

Do not begin orbit-fiber analysis, three-voter work, warrant semantics, Lean
formalization, or paper-claim promotion as a consequence of this result alone.

If the project instead treats the result as WEAK GO / CONDITIONAL GO after
review, the only next authorized work is a design for a three-voter semantic
`S_3` extension precheck.

## 15. Explicit Non-Claims

This result does not claim:

- an M4 theorem;
- a warrant-contract semantics;
- Lean formalization of semantic MUS/MCS;
- any Arrow result;
- any Gibbard-Satterthwaite result;
- any general social-choice theorem-family result;
- family-level CNF/LRAT/atlas/repair transfer;
- promotion of `/tmp` outputs to canonical tracked artifacts.
