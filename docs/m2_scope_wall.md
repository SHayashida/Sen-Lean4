# M2 Scope Wall: Proof Layer vs. Witness/Audit Layer

## Decision

M2 separates two claims that must not be collapsed:

1. The Lean Proof layer establishes a semantic Sen impossibility lift to full
   `SocialAcyclic`.
2. The CNF Witness/Audit layer certifies only the sen24-audited short-cycle
   encoding, namely `no_cycle3 ∧ no_cycle4`.

The scope wall is therefore between the Proof layer and the Witness/Audit layer,
not merely between a local-rationality theorem family and a full-acyclicity
theorem family.

## Proof Layer

`SocialChoiceAtlas/Sen/Lifting/ImpossibilityLift.lean` contains the M2 positive
bridge theorem:

```lean
theorem sen_impossibility_lifts
    {n m : ℕ} (_hn : 2 ≤ n) (_hm : 4 ≤ m)
    (F : SWF (Fin n) (Fin m))
    (hUN : UN F) (hMINLIB : MINLIB F) :
    ¬ SocialAcyclic F
```

This theorem is semantic. It uses the Lean definitions of `UN`, `MINLIB`,
`Decisive`, and `SocialAcyclic`; it does not route through the CNF
`no_cycle3` or `no_cycle4` levers. Its conclusion reaches full acyclicity at
the Proof layer for finite cases with at least two voters and at least four
alternatives.

## Witness/Audit Layer

The sen24 CNF artifacts certify a different object: the short-cycle encoding
`no_cycle3 ∧ no_cycle4`. The equivalence between that short-cycle encoding and
full acyclicity was audited only for the four-alternative sen24 setting by the
finite checker `scripts/check_acyclicity_short_cycles.py`.

For `m ≥ 5`, the audited equivalence does not transfer automatically. The
existing interpretation notes record that `no_cycle3 ∧ no_cycle4` still permits
length-5 cycles at `m = 5`, so the local clause family is not a family-level CNF
certificate for full `SocialAcyclic`.

## Consequence for M2

The Lean theorem proves that Sen's impossibility lifts at the semantic Proof
layer. It does not upgrade the sen24 CNF atlas into a family-level CNF
certificate for full acyclicity.

Accordingly, M2 can state both sides of the boundary:

- **Positive side:** the Lean Proof layer proves the semantic lift to full
  `SocialAcyclic`.
- **Negative side:** the CNF Witness/Audit layer remains scoped to the audited
  short-cycle encoding unless a stronger family-level rationality encoding is
  introduced and audited.

This preserves the Evidence/Transfer contract distinction: proof-level transfer
is kernel-checked, while witness-level transfer requires a separately audited
encoding contract.

## Non-goals

This note does not claim that:

- the CNF `no_cycle3 ∧ no_cycle4` witness lifts to full `SocialAcyclic` for
  `m ≥ 5`;
- the existing sen24 atlas is a family-level CNF certificate for full
  acyclicity;
- new solver experiments have been run;
- M1 or M1.5 paper claims have been changed.

## Pointers

- `docs/gates/m2/aim_signoff.md` records the M2 decision that the Proof layer
  reaches full acyclicity while the CNF Witness/Audit layer remains short-cycle
  scoped.
- `docs/no_cycle_interpretation_note.md` records that `no_cycle3 ∧ no_cycle4`
  permits length-5 cycles at `m = 5`.
- `docs/axiom_semantics_scaling.md` records the Step 0.5 policy: evidence using
  `no_cycle3` and `no_cycle4` is interpreted only within the corresponding
  local-rationality family, not as evidence about full acyclicity families.
