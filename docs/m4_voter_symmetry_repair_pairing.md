# M4 Voter Symmetry Repair Pairing

## Scope

This check uses the natural split-Sen24 lever-subset residual class:

```text
Q = all subsets of {asymm, un, decisive_voter0, decisive_voter1, no_cycle3, no_cycle4}
```

No arbitrary residual constraints are added. Bitstrings are written in the split-universe order:

```text
asymm, un, decisive_voter0, decisive_voter1, no_cycle3, no_cycle4
```

## Voter-Swap Map

Define the voter-swap map `tau` on split levers by:

| lever | tau(lever) |
|---|---|
| `asymm` | `asymm` |
| `un` | `un` |
| `decisive_voter0` | `decisive_voter1` |
| `decisive_voter1` | `decisive_voter0` |
| `no_cycle3` | `no_cycle3` |
| `no_cycle4` | `no_cycle4` |

For a residual `q`, `tau(q)` is obtained by applying `tau` pointwise to its active levers. For a repair set `R`, `tau(R)` is defined the same way.

In the case bitstring convention above, `tau` swaps the third and fourth bits and leaves all other bits fixed.

## Method

Fresh scratch run:

```bash
python3 scripts/run_candidate_b_minlib_granularity.py \
  --outdir /tmp/m4_voter_symmetry_repair_pairing \
  --solver cadical

python3 scripts/enumerate_repairs.py \
  --atlas /tmp/m4_voter_symmetry_repair_pairing/split/atlas.json \
  --atlas-out /tmp/m4_voter_symmetry_repair_pairing/split/atlas_with_repairs.json
```

Run metadata:

- Solver: `cadical` 3.0.0.
- Split status counts: `SAT = 62`, `UNSAT = 2`.
- Repair enumeration method: `axiom_level_full_enumeration_v1`.
- Processed UNSAT cases: `2`.
- Scratch outputs only; protected certificate artifacts were not modified.

## SAT Equivariance

For every natural split-Sen24 residual `q`, the scratch atlas satisfies:

```text
SAT(q) = SAT(tau(q))
```

Equivalently, every row below has matching status.

| q | tau(q) | status(q) | status(tau(q)) | equal | tau-fixed |
|---|---|---|---|---|---|
| `case_000000` | `case_000000` | SAT | SAT | yes | yes |
| `case_100000` | `case_100000` | SAT | SAT | yes | yes |
| `case_010000` | `case_010000` | SAT | SAT | yes | yes |
| `case_110000` | `case_110000` | SAT | SAT | yes | yes |
| `case_001000` | `case_000100` | SAT | SAT | yes | no |
| `case_101000` | `case_100100` | SAT | SAT | yes | no |
| `case_011000` | `case_010100` | SAT | SAT | yes | no |
| `case_111000` | `case_110100` | SAT | SAT | yes | no |
| `case_000100` | `case_001000` | SAT | SAT | yes | no |
| `case_100100` | `case_101000` | SAT | SAT | yes | no |
| `case_010100` | `case_011000` | SAT | SAT | yes | no |
| `case_110100` | `case_111000` | SAT | SAT | yes | no |
| `case_001100` | `case_001100` | SAT | SAT | yes | yes |
| `case_101100` | `case_101100` | SAT | SAT | yes | yes |
| `case_011100` | `case_011100` | SAT | SAT | yes | yes |
| `case_111100` | `case_111100` | SAT | SAT | yes | yes |
| `case_000010` | `case_000010` | SAT | SAT | yes | yes |
| `case_100010` | `case_100010` | SAT | SAT | yes | yes |
| `case_010010` | `case_010010` | SAT | SAT | yes | yes |
| `case_110010` | `case_110010` | SAT | SAT | yes | yes |
| `case_001010` | `case_000110` | SAT | SAT | yes | no |
| `case_101010` | `case_100110` | SAT | SAT | yes | no |
| `case_011010` | `case_010110` | SAT | SAT | yes | no |
| `case_111010` | `case_110110` | SAT | SAT | yes | no |
| `case_000110` | `case_001010` | SAT | SAT | yes | no |
| `case_100110` | `case_101010` | SAT | SAT | yes | no |
| `case_010110` | `case_011010` | SAT | SAT | yes | no |
| `case_110110` | `case_111010` | SAT | SAT | yes | no |
| `case_001110` | `case_001110` | SAT | SAT | yes | yes |
| `case_101110` | `case_101110` | SAT | SAT | yes | yes |
| `case_011110` | `case_011110` | SAT | SAT | yes | yes |
| `case_111110` | `case_111110` | SAT | SAT | yes | yes |
| `case_000001` | `case_000001` | SAT | SAT | yes | yes |
| `case_100001` | `case_100001` | SAT | SAT | yes | yes |
| `case_010001` | `case_010001` | SAT | SAT | yes | yes |
| `case_110001` | `case_110001` | SAT | SAT | yes | yes |
| `case_001001` | `case_000101` | SAT | SAT | yes | no |
| `case_101001` | `case_100101` | SAT | SAT | yes | no |
| `case_011001` | `case_010101` | SAT | SAT | yes | no |
| `case_111001` | `case_110101` | SAT | SAT | yes | no |
| `case_000101` | `case_001001` | SAT | SAT | yes | no |
| `case_100101` | `case_101001` | SAT | SAT | yes | no |
| `case_010101` | `case_011001` | SAT | SAT | yes | no |
| `case_110101` | `case_111001` | SAT | SAT | yes | no |
| `case_001101` | `case_001101` | SAT | SAT | yes | yes |
| `case_101101` | `case_101101` | SAT | SAT | yes | yes |
| `case_011101` | `case_011101` | SAT | SAT | yes | yes |
| `case_111101` | `case_111101` | UNSAT | UNSAT | yes | yes |
| `case_000011` | `case_000011` | SAT | SAT | yes | yes |
| `case_100011` | `case_100011` | SAT | SAT | yes | yes |
| `case_010011` | `case_010011` | SAT | SAT | yes | yes |
| `case_110011` | `case_110011` | SAT | SAT | yes | yes |
| `case_001011` | `case_000111` | SAT | SAT | yes | no |
| `case_101011` | `case_100111` | SAT | SAT | yes | no |
| `case_011011` | `case_010111` | SAT | SAT | yes | no |
| `case_111011` | `case_110111` | SAT | SAT | yes | no |
| `case_000111` | `case_001011` | SAT | SAT | yes | no |
| `case_100111` | `case_101011` | SAT | SAT | yes | no |
| `case_010111` | `case_011011` | SAT | SAT | yes | no |
| `case_110111` | `case_111011` | SAT | SAT | yes | no |
| `case_001111` | `case_001111` | SAT | SAT | yes | yes |
| `case_101111` | `case_101111` | SAT | SAT | yes | yes |
| `case_011111` | `case_011111` | SAT | SAT | yes | yes |
| `case_111111` | `case_111111` | UNSAT | UNSAT | yes | yes |

Orbit summary:

- Natural residuals checked: `64`.
- `tau`-fixed residuals: `32`.
- Non-fixed residuals: `32`, arranged as `16` two-cycles.
- Status mismatches under `tau`: `0`.

## UNSAT Repair Equivariance

The solved UNSAT residuals are:

- `case_111101`
- `case_111111`

Both are `tau`-fixed.

| q | tau(q) | RawRep(q) | tau(RawRep(q)) | RawRep(tau(q)) | equivariant |
|---|---|---|---|---|---|
| `case_111101` | `case_111101` | `{{no_cycle4}, {decisive_voter1}, {decisive_voter0}, {un}, {asymm}}` | `{{no_cycle4}, {decisive_voter0}, {decisive_voter1}, {un}, {asymm}}` | `{{asymm}, {un}, {decisive_voter0}, {decisive_voter1}, {no_cycle4}}` | yes |
| `case_111111` | `case_111111` | `{{no_cycle4}, {decisive_voter1}, {decisive_voter0}, {un}, {asymm}}` | `{{no_cycle4}, {decisive_voter0}, {decisive_voter1}, {un}, {asymm}}` | `{{asymm}, {un}, {decisive_voter0}, {decisive_voter1}, {no_cycle4}}` | yes |

Thus, for each UNSAT residual `q`:

```text
R in RawRep(q) iff tau(R) in RawRep(tau(q))
```

## Pairing Consequence

Every UNSAT `q` in the natural residual class satisfies:

```text
tau(q) = q
```

Together with repair equivariance, this implies:

```text
{decisive_voter0} in RawRep(q)
  iff tau({decisive_voter0}) in RawRep(q)
  iff {decisive_voter1} in RawRep(q)
```

Therefore voter-specific liberalism singleton repairs must appear as a pair for every UNSAT `tau`-fixed residual in this class.

## Conclusion

The split-Sen24 natural residual class is voter-swap symmetric at both the satisfiability and repair-explanation levels:

- `SAT(q) = SAT(tau(q))` for all `64` natural residuals.
- `R in RawRep(q) iff tau(R) in RawRep(tau(q))` for both UNSAT residuals.
- Every UNSAT residual is `tau`-fixed.
- Consequently, `{decisive_voter0}` and `{decisive_voter1}` repairs appear together rather than singly.

This explains the fiber-multiplicity collapse observed in the companion precheck: within this natural residual class, `mu(q, minlib)` is forced to be `0` or `2` for UNSAT `tau`-fixed cases, and the observed UNSAT cases both have value `2`.
