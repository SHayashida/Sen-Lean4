# M3/Sen24 Faithfulness Necessity Check

Status: exploratory precheck

Scope: Sen24 `n = 2`, `m = 4`, selector-free fixed-witness Decisive structure

Claim boundary: not a Lean theorem; no production encoder change

## Question

Check whether the Sen24 Decisive structure and the grouped-report beta can
collapse residual information.

For this precheck, a residual-collapse witness is:

```text
two Decisive witness wirings W1 and W2
with the same grouped residual mask T
such that SAT/UNSAT status differs after q collapses right atoms to minlib.
```

The grouped-report map is the existing M4 map:

```text
q_atom(asymm) = asymm
q_atom(un) = un
q_atom(no_cycle3) = no_cycle3
q_atom(no_cycle4) = no_cycle4
q_atom(right(voter,P)) = minlib
```

## Command

```bash
python3 scripts/exploration/m4/residual_class_coverage_certificate.py \
  --out-dir /tmp/sen_m4_residual_class_coverage_certificate_check \
  --solver cadical \
  --timeout 20
```

## Exhaustive Result

The run enumerated all `32` bundled residual masks and all `592` witness/status
rows. There were no `UNKNOWN` rows.

Aggregate mask statuses:

| aggregate status | count |
| --- | ---: |
| `ALL_W_SAT` | 21 |
| `ALL_W_UNSAT` | 2 |
| `MIXED` | 9 |
| `UNKNOWN` | 0 |

The existence of `MIXED` masks means that the grouped residual mask can hide
Decisive-witness information that changes satisfiability.

## Smallest Collapse Witness

The smallest mixed grouped residual mask is:

```text
case_10100 = {asymm, minlib}
```

Both rows have the same grouped residual mask because both fixed rights report
as `minlib`.

| grouped residual | Decisive wiring | shape | status |
| --- | --- | --- | --- |
| `{asymm, minlib}` | `right(voter0,{0,1})`, `right(voter1,{0,1})` | O2 | `UNSAT` |
| `{asymm, minlib}` | `right(voter0,{0,1})`, `right(voter1,{0,2})` | O3 | `SAT` |

Thus any shape-blind grouped residual predicate assigning a single truth value
to `{asymm, minlib}` fails to agree with at least one concrete Decisive wiring.

## Full Sen24 Top-Mask Boundary

The fully active Sen24 masks checked by the M4 residual-class certificate remain
uniformly UNSAT over all Decisive witness wirings:

```text
case_11101
case_11111
```

The separation occurs at residual subsets, not by making the fully active top
mask mixed. This still matters for M3 residual faithfulness, because
`ResidualFaithfulness` quantifies over all retained residual subsets.

## Conclusion

Under the stated criterion, a residual-collapsing wiring exists in the concrete
Sen24 `n = 2`, `m = 4` structure. The shape-blind grouped beta is therefore
not faithful in this residual-status sense: Sen24 is not a benign case where
all grouped wirings preserve residual distinctions.

Remaining work: formalize the corresponding M3 witness, and separately check or
prove the stronger grouped-correctness failure statement if that is needed for
the theorem-core audit.
