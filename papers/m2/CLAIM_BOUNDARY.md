# M2 Claim Boundary

This file is the paper-specific claim boundary for the M2 manuscript
(Bridge Theorems / Transfer Contract).

## Authorized Claims

M2 authorizes exactly three paper-level claims.

1. **Generic semantic obstruction bridge.** For any voter type and any finite
   alternative type represented by the repository's ranking interface,
   semantic `UN` and `MINLIB` yield a classified bounded semantic obstruction.
   The exhaustive canonical family is O2/O3/O4, with exact support
   cardinalities 2/3/4 and outcomes strict conflict / 3-cycle / 4-cycle.
   The bridge theorem is
   `sen_outcome_obstruction_of_UN_MINLIB` at
   `SocialChoiceAtlas/Sen/ObstructionBridge.lean`.
2. **Generic impossibility and compatibility corollary.** The obstruction
   bridge yields `¬ SocialAcyclic F` through
   `sen_impossibility_from_obstruction_basis`. The existing
   `sen_impossibility_lifts` theorem for `(Fin n, Fin m)` is retained as a
   kernel-checked compatibility corollary at
   `SocialChoiceAtlas/Sen/Lifting/ImpossibilityLift.lean`.
3. **Witness/Audit scope wall.** The semantic bridge does **not** upgrade the
   Sen24 short-cycle CNF, LRAT certificate, atlas, or repair family into
   family-level artifacts. The CNF Witness/Audit layer certifies only the
   sen24-audited short-cycle encoding `no_cycle3 ∧ no_cycle4`, whose
   equivalence to full acyclicity was audited only at four alternatives. See
   `docs/m2_scope_wall.md`.

## Basis Terminology

"Finite semantic obstruction basis" means a complete finite generating family
of semantic obstruction shapes. No minimality or irredundancy theorem is
claimed.

The general theorem is not obtained by treating the Sen24 CNF artifact as a
formal premise. The connection is through the shared bounded semantic
obstruction shapes that also appear in the Sen24 proof pattern.

## Non-claims

M2 does **not** claim:

- a literal two-voter Sen24 subinstance inside every general instance;
- a family-level CNF certificate for full `SocialAcyclic`;
- that the Sen24 LRAT proof certifies the general theorem family;
- that the O2/O3/O4 basis is minimal, unique, or irredundant;
- a canonical lift of repair families, MUS/MCS geometry, or atlas geometry;
- a representation-non-canonicity theorem at family scale;
- new solver experiments;
- any modification of M1, M1.5, M2.1, or M3 paper claims;
- Arrow-family generality.

Representation non-canonicity at family scale (Negative #2) remains a separate
milestone **M2.1**. In this manuscript it appears only as a forward pointer in
Discussion / Future Work and must not be allocated a main-results section.

## Binding Wording for Legacy Size Hypotheses

The generic obstruction theorem has no explicit voter- or
alternative-cardinality lower-bound hypotheses. Its public assumptions are an
arbitrary voter type, a finite decidable alternative type, semantic `UN`, and
semantic `MINLIB`.

The legacy theorem
`SocialChoiceAtlas.Sen.Lifting.sen_impossibility_lifts` keeps
`_hn : 2 ≤ n` and `_hm : 4 ≤ m` solely for backward-compatible alignment with
the former `(Fin n, Fin m)` statement. Its proof body is now the specialization
of `sen_impossibility_from_obstruction_basis`.

Manuscript prose must preserve the following discipline:

- **Forbidden formulations.** Do not write that `UN ∧ MINLIB` implies
  `4 ≤ m`, that `_hm` is implied by the other hypotheses, or that the generic
  theorem consumes explicit lower-bound hypotheses.
- **Required formulation.** The generic obstruction theorem does not require
  explicit lower-bound hypotheses. The legacy theorem retains `_hn` and `_hm`
  for API compatibility and statement continuity only. This is not a claim
  that `UN ∧ MINLIB` logically implies `4 ≤ m`.

## Artifact Binding

Each authorized claim is bound to a path or kernel-checked module:

| Claim | Binding |
|---|---|
| Witness extraction / classification | `SocialChoiceAtlas/Sen/ObstructionBasis.lean` |
| Generic profiles | `SocialChoiceAtlas/Sen/ObstructionProfiles.lean` |
| Exact support cardinalities and shape soundness | `SocialChoiceAtlas/Sen/ObstructionSoundness.lean` |
| Generic outcome bridge | `SocialChoiceAtlas/Sen/ObstructionBridge.lean` (`sen_outcome_obstruction_of_UN_MINLIB`) |
| Generic impossibility | `SocialChoiceAtlas/Sen/ObstructionBridge.lean` (`sen_impossibility_from_obstruction_basis`) |
| Legacy compatibility corollary | `SocialChoiceAtlas/Sen/Lifting/ImpossibilityLift.lean` (`sen_impossibility_lifts`) |
| Default kernel build | `SocialChoiceAtlas.lean` (root import lines) |
| M2 smoke gate | `scripts/ci_m2_smoke.sh` |
| Witness/Audit scope wall | `docs/m2_scope_wall.md` |
| Short-cycle scaling note | `docs/no_cycle_interpretation_note.md` |
| Step 0.5 sign-off | `docs/axiom_semantics_scaling.md` |

## Reproduction Record Requirements

Before any M2 manuscript freeze, record:

1. the commit hash on the M2 bridge branch;
2. the submission tag, if any;
3. `lake env lean SocialChoiceAtlas/Sen/ObstructionBridge.lean`;
4. `lake env lean SocialChoiceAtlas/Sen/Lifting/ImpossibilityLift.lean`;
5. `./scripts/ci_m2_smoke.sh`;
6. `lake build`;
7. `make -C papers/m2 pdf`;
8. the artifact binding table above.

## Non-goal (Scope Hygiene)

This file does not change or broaden the claim boundary of the existing M1
manuscript under `paper/`, the M1.5 manuscript under `papers/m1_5/`, the M2.1
workspace under `papers/m2_1/`, or the M3 workspace under `papers/m3/`.
