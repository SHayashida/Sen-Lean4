# M4 Fiber Multiplicity Precheck

## Question

Check whether the natural Sen24 residual class, using the split lever universe

```text
asymm, un, decisive_voter0, decisive_voter1, no_cycle3, no_cycle4
```

contains an UNSAT residual `q` for which exactly one voter-specific liberalism repair is inclusion-minimal.

The coarse grouping used for the liberalism fiber is:

```text
decisive_voter0, decisive_voter1 -> minlib
```

For an UNSAT residual `q`, this note writes `RawRep(q)` for the inclusion-minimal lever removals `R` such that `q \ R` is SAT, and computes:

```text
mu(q, minlib) = |RawRep(q) cap {{decisive_voter0}, {decisive_voter1}}|
```

## Method

Fresh scratch run:

```bash
python3 scripts/run_candidate_b_minlib_granularity.py \
  --outdir "${TMPDIR:-/tmp}/m4_candidate_b_minlib_granularity" \
  --solver cadical

python3 scripts/enumerate_repairs.py \
  --atlas "${TMPDIR:-/tmp}/m4_candidate_b_minlib_granularity/split/atlas.json" \
  --atlas-out "${TMPDIR:-/tmp}/m4_candidate_b_minlib_granularity/split/atlas_with_repairs.json"
```

Run metadata:

- Split universe: `asymm, un, decisive_voter0, decisive_voter1, no_cycle3, no_cycle4`.
- Base case: `n = 2`, `m = 4`.
- Split status counts: `SAT = 62`, `UNSAT = 2`.
- Repair enumeration method: `axiom_level_full_enumeration_v1`.
- Processed UNSAT cases: `2`.
- Protected certificate artifacts were not modified.

All one-sided split cases, where exactly one of `decisive_voter0` and `decisive_voter1` is present, were SAT in this run. Thus the UNSAT list below is the same whether the natural class is read as all 64 split subsets or as the coarse-natural image where the two decisive levers are both present or both absent.

## Results

Bitstrings are in the split-universe order shown above.

| q | Active levers | RawRep(q) | mu(q, minlib) |
|---|---|---|---:|
| `case_111101` | `{asymm, un, decisive_voter0, decisive_voter1, no_cycle4}` | `{{no_cycle4}, {decisive_voter1}, {decisive_voter0}, {un}, {asymm}}` | 2 |
| `case_111111` | `{asymm, un, decisive_voter0, decisive_voter1, no_cycle3, no_cycle4}` | `{{no_cycle4}, {decisive_voter1}, {decisive_voter0}, {un}, {asymm}}` | 2 |

Coarsened forms:

- `case_111101` maps to `{asymm, un, minlib, no_cycle4}`.
- `case_111111` maps to `{asymm, un, minlib, no_cycle3, no_cycle4}`.

## Conclusion

No solved UNSAT residual `q` has `mu(q, minlib) = 1`.

Observed collapse pattern:

```text
mu(q, minlib) in {0, 2} for all UNSAT q
```

In this Sen24 split precheck, the two UNSAT residuals both have `mu(q, minlib) = 2`: the singleton repairs `{decisive_voter0}` and `{decisive_voter1}` appear together, never exactly one at a time.
