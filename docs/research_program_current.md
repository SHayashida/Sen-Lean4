# Current Research Program

## Canonical status

- Repository: `SHayashida/Sen-Lean4`
- Canonical branch: `main`
- Scientific baseline commit for this update:
  `be4132ba3b6f8168b75644e0928d7b2609048049`
- Program status date: 2026-07-02
- Dissertation scope: `docs/doctoral_scope_lock.md`

## 1. Program thesis

Machine-verified correctness does not by itself license generalization, repair
reporting, or institutional action. Each transition requires a distinct
abstraction contract and an associated preservation theorem.

The repository tracks those obligations separately: truth claims, generated or
audited artifacts, grouped reporting claims, and the future warrant layer for
institutional action are not interchangeable.

## 2. Canonical milestone table

| Milestone | Scientific result | Canonical remote state | Next action |
|---|---|---|---|
| M1 | Audited finite Sen24 evidence; Proof/Audit/Witness/Assumption separation | Canonical on `main` | Preserve claim boundary |
| M1.5 | Raw repair non-canonicity under controlled representation comparison | Result and manuscript workspace present | Publication-unit design with M3 |
| M2 | Generic O2/O3/O4 semantic obstruction bridge and general Sen theorem | Canonical, tagged, DOI archived; reviewer audit complete | Required major manuscript revision before submission |
| M2.1 | Alternative-dimension persistence and voter-dimension boundary | Evidence/scripts partly canonical through PR #9; manuscript not canonical | Defer separate paper integration |
| M3 | M3-A/B/C finite-set reportability theorem core | Canonical on `main` through PR #16 | Refresh docs; package Candidate B evidence separately |
| Candidate B | Artifact-defined M3-B instantiation | Reconstructed off-main; not canonical on `main` | Curated evidence package and validator or release binding |
| M4 | M4/Sen24 claim-boundary preprint workspace; institutional warrant theorem remains future work | Local v0.1 RC workspace exists under `papers/m4/`; not a public release | External claim-boundary review without broadening claims |

Candidate B is an application/status row under M3, not a sixth dissertation
milestone.

M1.5 and M3 publication packaging is not final.

## 3. M4 local RC workspace status

`papers/m4/` is a local v0.1 release-candidate preprint workspace for a
claim-boundary audit under the declared M4/Sen24 encoding. It records
finite-audit replay evidence and a Lean right-atom bridge check.

This workspace is not an arXiv, Zenodo, jxiv, GitHub Release, or pushed-tag
public release. It does not claim Level C semantic-to-CNF correctness,
Python/CNF correctness, checker formalization in Lean, a fully Lean-verified
finite certificate, a new general Sen theorem, family-scale lift, or an AI
governance/alignment solution.

## 4. M2 canonical archival identity

```text
Tag:
papers-m2-v2-obstruction-bridge

Archived commit:
d7e5fd1ac94ab18330951b5d9741585dddc5b43a

GitHub Release:
https://github.com/SHayashida/Sen-Lean4/releases/tag/papers-m2-v2-obstruction-bridge

Zenodo version DOI:
https://doi.org/10.5281/zenodo.20796920

Zenodo concept DOI:
https://doi.org/10.5281/zenodo.20468649
```

Zenodo preserves the tagged source snapshot. The GitHub Release preserves the
extended release assets. Post-release DOI documentation is outside the tagged
source snapshot. The tag must not be moved.

## 5. Current bridge status

| Bridge object | Current status |
|---|---|
| Semantic obstruction bridge | Established |
| General Sen impossibility theorem | Established |
| Sen24 CNF family lift | Not lifted |
| Sen24 LRAT family lift | Not lifted |
| Finite-atlas family lift | Not lifted |
| Repair/MCS family lift | Not lifted |

M2 derives the general theorem from a finite semantic obstruction
classification, not from the Sen24 CNF as a formal premise.

## 6. Prior M2 audit notes

The one-time M2 reviewer audit was merged through PR #14.

| Audit component | Verdict |
|---|---|
| Literature novelty audit | `MODERATE` |
| Adversarial review | `PASS WITH MAJOR REVISION` |
| Submission-unit decision | `CONDITIONAL GO` |

Standalone M2 remains the primary submission unit, but only after the required
major manuscript revision. The audit identifies Social Choice and Welfare as
the primary venue. Journal of Automated Reasoning remains a fallback only if the
paper is reframed more strongly around formal methods.

No new theorem or experiment is required for the minimum viable M2 submission.
The manuscript revision remains separate from the main research track.

Audit documents:

- `docs/m2_literature_novelty_audit.md`
- `docs/m2_adversarial_review.md`
- `docs/m2_submission_unit_decision.md`

## 7. M3 canonical theorem-core status

The abstract M3 finite-set reportability theorem core is canonical on `main`.

Provenance:

- integration precheck PR #15 merge commit:
  `7781d293ec785e38d6d434b10d1d9d87e29f70ae`;
- theorem-core PR #16 merge commit:
  `be4132ba3b6f8168b75644e0928d7b2609048049`;
- audited source branch:
  `origin/codex/m3-lean-reportability`;
- audited source SHA:
  `1c2b9e7b979ba1a4b08c1d69f5400907cf2ca689`;
- integration strategy:
  clean file extraction plus patch-only root imports.

Canonical modules:

- `SocialChoiceAtlas/Reportability/Defs.lean`
- `SocialChoiceAtlas/Reportability/Atomic.lean`
- `SocialChoiceAtlas/Reportability/GroupSound.lean`
- `SocialChoiceAtlas/Reportability/Monotone.lean`
- `SocialChoiceAtlas/Reportability/Examples.lean`

Focused gate:

- `scripts/ci_m3_smoke.sh`

The expected standard axiom set for the main M3 declarations is:

```text
[propext, Classical.choice, Quot.sound]
```

The integration precheck and focused smoke gate found no unexpected custom
axioms. The M3 Lean modules do not formalize Candidate B artifacts.

| Layer | Canonical result |
|---|---|
| M3-A | Atomicity plus residual faithfulness yields grouped correctness; raw transport is available under atomic realizations |
| M3-B | GroupSoundness plus residual faithfulness yields grouped correctness without atomicity |
| M3-C | Under reference deletion monotonicity, grouped correctness implies GroupSoundness |
| Exactness | `groupSoundness_iff` under its Lean assumptions |
| Hierarchy | Atomicity implies GroupSoundness under the M3-A assumptions |
| Boundary examples | Atomicity is not necessary; monotonicity cannot simply be removed |

The core is abstract and contract-relative. It does not establish semantic
validity of social-choice contract atoms.

## 8. Candidate B application status

The integration precheck in `docs/m3_canonical_integration_precheck.md`
independently reconstructed the Candidate B artifact audit:

- the 16 block-aligned residual comparisons were reconstructed;
- the fully active bundled and split cases are UNSAT;
- the 15 proper bundled residuals are SAT;
- five split singleton repairs are SAT;
- the grouped family is `{asymm}`, `{un}`, `{minlib}`, `{no_cycle4}`.

This evidence remains off-main. No dedicated canonical validator exists yet.
Candidate B is not canonical until evidence binding is completed through either:

- a curated evidence package plus canonical validator; or
- immutable release binding.

Candidate B is artifact-defined. Its artifact evidence remains outside the M3
Lean theorem core, and it does not establish semantic or Lean-level validity of
the contract atoms.

## 9. Publication-unit status

- M2 standalone publication decision is `CONDITIONAL GO`; required major
  manuscript revision remains before submission.
- M1.5 and M3 may form an integrated paper.
- No final M1.5+M3 publication unit has been locked.
- No canonical `papers/m3/` workspace exists.
- `papers/m4/` is a local RC preprint workspace for claim-boundary review, not
  a public release.
- M2.1 remains separate and deferred.
- Publication packaging does not alter the dissertation spine.

## 10. Active next actions

1. Use the M4/Sen24 local RC workspace for claim-boundary review while keeping
   public-release and Level C obligations explicit.
2. Revise and integrate current M3 documentation.
3. Create the Candidate B curated evidence package and validator, or bind an
   immutable release.
4. Complete the required M2 manuscript revision before submission.
5. Decide and develop the M1.5+M3 publication unit.
6. Defer M2.1 paper integration and maintenance cleanup.

The future institutional-warrant M4 theorem remains a separate theoretical
track. Items 2-6 are parallel or publication-governance tracks.

## 11. Non-blocking backlog

- M3 linter-warning cleanup, only in a separately audited code task.
- Stale M3 skeleton retention/archival policy.
- Candidate B release packaging.
- M2 manuscript major revision.
- M2.1 publication packaging.
- Legacy M2 helper cleanup.
- macOS portability maintenance.
- Optional full-asset Zenodo enrichment.
- Historical branch cleanup only after archival review.

## 12. Source-of-truth hierarchy

1. Paper-specific claim-boundary files govern individual paper claims.
2. `docs/doctoral_scope_lock.md` governs dissertation scope.
3. `docs/research_program_current.md` governs current program status.
4. `RESEARCH_STATUS.md` is a concise operational summary.
5. `README.md` is a public overview and does not broaden any claim.
