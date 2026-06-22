# M2 Paper Workspace

This directory is the dedicated manuscript workspace for the third paper (M2:
Bridge Theorems / Transfer Contract).

## Scope

M2 ships three coordinated deliverables:

1. **Generic semantic obstruction bridge:** semantic `UN` and `MINLIB` yield a
   bounded classified obstruction in the finite O2/O3/O4 family
   (`SocialChoiceAtlas/Sen/ObstructionBridge.lean`).
2. **Generic impossibility and legacy compatibility:** the obstruction bridge
   refutes `SocialAcyclic`, and the existing
   `sen_impossibility_lifts` theorem over `(Fin n, Fin m)` is retained as a
   compatibility corollary
   (`SocialChoiceAtlas/Sen/Lifting/ImpossibilityLift.lean`).
3. **Witness/Audit scope wall:** the semantic bridge does not lift the Sen24
   CNF, LRAT, atlas, or repair artifacts to family-level artifacts
   (`docs/m2_scope_wall.md`).

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

## Paper-specific Contract

- Claim boundary: `papers/m2/CLAIM_BOUNDARY.md`
- Reproducibility note: `papers/m2/REPRODUCIBILITY.md`
- Zenodo release note: `papers/m2/ZENODO.md`

These files must remain specific to M2 and must not silently expand the claim
scope of `paper/` (M1), `papers/m1_5/` (M1.5), `papers/m2_1/` (M2.1), or
`papers/m3/` (M3).

## Shared Code/Data Policy

- Shared scripts, Lean code, and common data remain in the repository root
  layout.
- The generic bridge lives under:
  - `SocialChoiceAtlas/Sen/ObstructionBasis.lean`
  - `SocialChoiceAtlas/Sen/ObstructionProfiles.lean`
  - `SocialChoiceAtlas/Sen/ObstructionSoundness.lean`
  - `SocialChoiceAtlas/Sen/ObstructionBridge.lean`
- The legacy compatibility theorem lives at
  `SocialChoiceAtlas/Sen/Lifting/ImpossibilityLift.lean`.
- The modules are kernel-checked by default `lake build` via the root imports
  in `SocialChoiceAtlas.lean` and gated by `scripts/ci_m2_smoke.sh`.
- M2 should point to explicit Lean module paths, decision-record paths, and
  scope-wall paths for any paper claim.

## Public Repo Safety

- No local absolute paths, secrets, or private tokens in manuscript text or
  generated assets.
- Follow `docs/public_repo_security.md`.
- Keep protected baseline artifacts unchanged
  (`Certificates/sen24.*`, `Certificates/atlas/case_11111/**`).

## Inherited Prose Discipline

- **Do** say that the Proof layer now factors through a finite semantic
  obstruction basis: O2/O3/O4 with exact support cardinalities 2/3/4 and
  outcomes strict conflict / 3-cycle / 4-cycle.
- **Do** say that "basis" means a complete finite generating family, with no
  minimality or irredundancy claim.
- **Do** say that the legacy `(Fin n, Fin m)` theorem retains `_hn` and `_hm`
  only for API compatibility with the former statement.
- **Do not** say that `UN ∧ MINLIB` implies `4 ≤ m`.
- **Do not** say that the Sen24 CNF, LRAT, atlas, or repair artifacts lift to
  the general family.
- **Do not** say that every general instance contains a literal two-voter
  Sen24 subinstance.

See `papers/m2/CLAIM_BOUNDARY.md` for the binding wording.
