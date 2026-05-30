# M2 Paper Workspace

This directory is the dedicated manuscript workspace for the third paper (M2:
Bridge Theorems / Transfer Contract).

## Scope

M2 ships **two** deliverables, ratified in `docs/gates/m2/aim_signoff.md`:

1. **Positive flagship:** the Lean Proof-layer semantic lift theorem
   `sen_impossibility_lifts` (kernel-checked at
   `SocialChoiceAtlas/Sen/Lifting/ImpossibilityLift.lean`).
2. **Negative #1 (scope wall):** the Proof-layer vs. CNF Witness/Audit-layer
   boundary (`docs/m2_scope_wall.md`).

Candidate-B representation non-canonicity at family scale (Negative #2) is
**deferred to M2.1** and appears here only as a forward pointer in Discussion /
Future Work. Do not introduce a full main-results section for it in this
workspace.

## Build

From repository root:

```bash
make -C papers/m2 pdf
```

Output PDF and auxiliary files are written under `papers/m2/build/`.

## Paper-specific contract

- Claim boundary: `papers/m2/CLAIM_BOUNDARY.md`
- Reproducibility note: `papers/m2/REPRODUCIBILITY.md`

These files must remain specific to M2 and must not silently expand the claim
scope of `paper/` (M1) or `papers/m1_5/` (M1.5).

## Shared code/data policy

- Shared scripts, Lean code, and common data remain in the repository root
  layout. The Lean defs for the lift live under `SocialChoiceAtlas/Sen/Lifting/`
  and are kernel-checked by default `lake build` via the root import in
  `SocialChoiceAtlas.lean` (Decision 3).
- The lift theorem is *not* copied into this workspace; it is referenced.
- M2 should point to explicit Lean module paths, decision-record paths, and
  scope-wall paths for any paper claim.

## Public repo safety

- No local absolute paths, secrets, or private tokens in manuscript text or
  generated assets.
- Follow `docs/public_repo_security.md`.
- Keep protected baseline artifacts unchanged
  (`Certificates/sen24.*`, `Certificates/atlas/case_11111/**`).

## Inherited prose discipline (`_hm` wording)

The lifting module establishes a *single* canonical formulation of why the
hypothesis `_hm : 4 ≤ m` is not consumed by the proof. All M2 prose
(manuscript, README, claim boundary, reproducibility) must inherit that
formulation verbatim:

- **Do not** say that `UN ∧ MINLIB` implies `4 ≤ m`.
- **Do not** describe `_hm` as redundant on logical-implication grounds.
- **Do** say that the proof does not consume `_hm`; the overlap case
  analysis avoids requiring four-point completion: two-overlap yields an
  asymmetry contradiction, one-overlap yields a 3-cycle, and disjointness
  yields a 4-cycle.

See `papers/m2/CLAIM_BOUNDARY.md` for the binding wording.
