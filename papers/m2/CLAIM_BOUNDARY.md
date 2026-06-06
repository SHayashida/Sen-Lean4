# M2 Claim Boundary

This file is the paper-specific claim boundary for the M2 manuscript
(Bridge Theorems / Transfer Contract).

## Authorized claims

M2 authorizes exactly two paper-level claims:

1. **Positive flagship (kernel-checked).** A Lean Proof-layer semantic lift of
   Sen's impossibility from the Sen24 base case `(Fin 2, Fin 4)` to any finite
   case `(Fin n, Fin m)` with `2 ≤ n` and `4 ≤ m`, satisfying semantic `UN` and
   `MINLIB`, concludes `¬ SocialAcyclic F`. The theorem is
   `sen_impossibility_lifts` at
   `SocialChoiceAtlas/Sen/Lifting/ImpossibilityLift.lean` and is exercised by
   default `lake build` via the root import in `SocialChoiceAtlas.lean`.
2. **Negative #1 (scope wall).** The Proof-layer lift does **not**
   automatically upgrade the sen24 CNF atlas into a family-level CNF
   certificate. The CNF Witness/Audit layer certifies only the sen24-audited
   short-cycle encoding `no_cycle3 ∧ no_cycle4`, whose equivalence to full
   acyclicity was audited only at four alternatives. For `m ≥ 5` the audited
   equivalence does not transfer automatically. See `docs/m2_scope_wall.md`.

## Non-claims (deferred to M2.1)

M2 does **not** claim:

- a representation-non-canonicity (Candidate-B) result at family scale;
- a new MUS/MCS or repair-canonicalization theorem at family scale;
- a family-level CNF certificate for full `SocialAcyclic`;
- new solver experiments;
- any modification of M1 or M1.5 paper claims.

Representation non-canonicity at family scale (Negative #2) is ratified as a
separate milestone **M2.1**. In this manuscript it appears only as a forward
pointer in Discussion / Future Work and must not be allocated a main-results
section.

## Binding wording for the `_hm : 4 ≤ m` hypothesis

The lifting module establishes the canonical formulation. Manuscript prose
must inherit it verbatim and must not paraphrase it into a stronger claim:

- **Forbidden formulations.** Do not write that `UN ∧ MINLIB` implies
  `4 ≤ m`, or that `_hm` is "implied" by the other hypotheses, or that
  `_hm` is consumed only "in the disjoint case" without scope qualification.
- **Required formulation.** The proof does not consume `_hm`; the overlap
  case analysis avoids requiring four-point completion:
  - **two-overlap** gives an asymmetry contradiction,
  - **one-overlap** gives a 3-cycle,
  - **disjointness** gives a 4-cycle.
  The hypothesis `_hm` is kept for statement symmetry with Sen's original
  formulation and to document the lift scope, but it is not consumed by
  `sen_impossibility_lifts`. The completion lemma
  `exists_not_mem_of_card_lt` and the cardinality bridge `four_le_card_fin`
  are retained as honest infrastructure documenting an avoided proof risk;
  neither is used by the final theorem.

## Artifact binding

Each authorized claim is bound to a path or kernel-checked module:

| Claim | Binding |
|---|---|
| Positive flagship | `SocialChoiceAtlas/Sen/Lifting/ImpossibilityLift.lean` (theorem `sen_impossibility_lifts`) |
| Default kernel build | `SocialChoiceAtlas.lean` (root import line) |
| Negative #1 (scope wall) | `docs/m2_scope_wall.md` |
| Decision record | `docs/gates/m2/aim_signoff.md` (D1, D2, D3 LANDED; D4 RATIFIED-DEFERRED → M2.1) |
| Short-cycle scaling note | `docs/no_cycle_interpretation_note.md` |
| Step 0.5 sign-off | `docs/axiom_semantics_scaling.md` |

## Reproduction record requirements

Before any M2 manuscript freeze, record:

1. the commit hash on `codex/m2-bridge`;
2. the submission tag (if any);
3. the `lake build` command used to exercise the lift module;
4. the `./scripts/ci_m2_smoke.sh` invariant outcome;
5. the artifact binding table above.

## Non-goal (scope hygiene)

This file does not change or broaden the claim boundary of the existing M1
manuscript under `paper/` or the M1.5 manuscript under `papers/m1_5/`.
