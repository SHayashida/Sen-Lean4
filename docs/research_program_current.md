# Current Research Program

## Canonical status

- Repository: `SHayashida/Sen-Lean4`
- Canonical branch: `main`
- Canonical main commit at this update: `9162b44b6db11601a4d751e1b869faa4f741381d`
- Program status date: 2026-06-26
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
| M1.5 | Raw repair non-canonicity under controlled representation comparison | Manuscript and evidence present in repository history | Publication-unit review with M3 |
| M2 | Generic O2/O3/O4 semantic obstruction bridge and general Sen theorem | Canonical on `main`; tagged and DOI archived | One-time reviewer audit |
| M2.1 | Alternative-dimension persistence and voter-dimension boundary | Evidence/scripts merged through PR #9; manuscript scaffold not canonical on `main` | Defer clean paper integration |
| M3 | M3-A/B/C finite-set reportability theory and Candidate B audit | Remote development branch only; not canonical on `main` | Clean integration precheck |
| M4 | Institutional warrant / delegated warrant preservation | No canonical remote implementation | Begin only after M2 audit and M3 integration |

M1.5 and M3 publication packaging is not final.

## 3. M2 canonical archival identity

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

## 4. Current bridge status

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

## 5. M3 remote status

- Remote branch: `origin/codex/m3-lean-reportability`
- Current remote branch head SHA:
  `1c2b9e7b979ba1a4b08c1d69f5400907cf2ca689`
- Merge base with `origin/main`:
  `73c891fa3edd96148238570f16453c484fccf283`
- M3 Lean modules present on the branch:
  - `SocialChoiceAtlas/Reportability/Defs.lean`
  - `SocialChoiceAtlas/Reportability/Atomic.lean`
  - `SocialChoiceAtlas/Reportability/GroupSound.lean`
  - `SocialChoiceAtlas/Reportability/Monotone.lean`
  - `SocialChoiceAtlas/Reportability/Examples.lean`
- Candidate B audit status:
  `docs/m3_candidate_b_group_soundness_audit_result.md` exists on the remote
  development branch.
- Canonical integration status: not canonical on `main`.

The M3 mathematical and Lean theorem core exists on a remote development
branch, but it is not a canonical `main` result until a dedicated integration
PR has reviewed its code, documentation, evidence bindings, and stale planning
state.

Do not describe the entire M3 branch as ready to merge wholesale. The branch
mixes M3 code/docs with other material and therefore requires a selective
integration precheck.

## 6. Publication-unit status

- M2 is currently treated as a standalone submission unit subject to a one-time
  novelty/adversarial/submission review.
- M1.5 and M3 may form an integrated publication unit.
- That publication decision is not locked by this document.
- M2.1 remains a separate companion/boundary-paper candidate.
- Publication packaging does not alter the dissertation spine.

## 7. Active next actions

1. M2 literature novelty audit.
2. M2 adversarial manuscript review.
3. M2 submission-unit decision.
4. M3 canonical integration precheck.
5. Clean M3 theorem-core integration into `main`.
6. Begin M4 warrant-contract skeleton.
7. Develop M1.5+M3 integrated manuscript in parallel.
8. Defer M2.1 publication integration and maintenance cleanup.

The first five items are required before M4 becomes the main implementation
track.

## 8. Non-blocking backlog

- Legacy M2 helper cleanup.
- macOS Unicode-range grep portability.
- Optional full-asset Zenodo enrichment.
- Historical branch cleanup only after archival review.
- M2.1 publication packaging.

None blocks the M2 reviewer audit.

## 9. Source-of-truth hierarchy

1. Paper-specific claim-boundary files govern individual paper claims.
2. `docs/doctoral_scope_lock.md` governs dissertation scope.
3. `docs/research_program_current.md` governs current program status.
4. `RESEARCH_STATUS.md` is a concise operational summary.
5. `README.md` is a public overview and does not broaden any claim.
