# Current Research Program

## Canonical status

- Repository: `SHayashida/Sen-Lean4`
- Canonical branch: `main`
- Inspected GitHub `main` HEAD and current repository baseline:
  `e33805d0ff0a64f12e450ba7aaa150729901d7d2`
- Latest theorem milestone commit:
  `be4132ba3b6f8168b75644e0928d7b2609048049`
- Latest manuscript milestone: completed M3 prior-art/manuscript
  synchronization and current-paper freeze.
- Program status date: 2026-09-27
- Potential doctoral-scope candidate record (not an enrollment or accepted-plan
  claim): `docs/doctoral_scope_lock.md`

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
| M1.5 | Raw repair non-canonicity under controlled representation comparison | Result, manuscript workspace, and C1-C5 witness binding canonical on `main` | Preserve the frozen integrated-paper claim boundary |
| M2 | Generic O2/O3/O4 semantic obstruction bridge and general Sen theorem | Canonical, tagged, DOI archived; reviewer audit complete | Required major manuscript revision before submission |
| M2.1 | Alternative-dimension persistence and voter-dimension boundary | Evidence/scripts partly canonical through PR #9; manuscript not canonical | Defer separate paper integration |
| M3 | M3-A/B/C finite-set reportability theorem core | Current-paper theory complete; prior-art matrix and integrated manuscript synchronized | Decide publication timing or submission preparation without reopening theory by default |
| Candidate B | Artifact-defined M3-B instantiation | Canonical validator-backed, self-contained application package on `main` under `m3/candidate_b/`; not Lean-verified or semantically validated | Release review after license and redistribution gates |
| Dafny pilot | Formal-model-repair workflow minimum example | Public external pilot at `SHayashida/dafny-m3-repair` commit `208c2a59aa24fc1d2befe22842a7b07af8ced576` | Add multiple cases and real-workflow evidence |
| XAI companion | Deferred or parallel companion track | No public artifact status is established by the inspected Sen `main` branch | Do not infer status until explicitly published |
| M4 | Institutional warrant / authority configuration | Future/deferred theory track; repository-local Sen24 RC exists under `papers/m4/` | Keep outside the immediate publication track |

Candidate B is an application/status row under M3, not an additional program
milestone.

M1.5 and M3 now have a canonical integrated CPP 2027 working-draft workspace
and a current-paper scope freeze. The research claim boundary is frozen, but
the paper is not represented as accepted or submission-ready.

## 3. M4 repository-local RC workspace status

`papers/m4/` is a repository-local v0.1 release-candidate preprint workspace
for a claim-boundary audit under the declared M4/Sen24 encoding. It records
finite-audit replay evidence and a Lean right-atom bridge check.

The workspace is bound by tag `papers-m4-v0.1-rc1`, but no matching GitHub
Release was found and no arXiv, Zenodo, or jxiv release is documented on the
inspected `main`. It does not claim Level C semantic-to-CNF correctness,
Python/CNF correctness, checker formalization in Lean, a fully Lean-verified
finite certificate, a new general Sen theorem, family-scale lift, or an AI
governance/alignment solution.

This RC is not the immediate publication track. The institutional-warrant M4
theorem remains future work.

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

For M2, the standalone manuscript remains its selected submission unit, but
only after the required major revision. It is not the program's immediate
submission track. The audit identifies Social Choice and Welfare as the primary
venue. Journal of Automated Reasoning remains a fallback only if the paper is
reframed more strongly around formal methods.

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

The current-paper stopping point, prior-art synchronization, deferred theorem
queue, and re-entry rule are recorded in `docs/m3_current_paper_freeze.md`.
The advisor-facing research delta is summarized in
`docs/advisor/m3_prior_art_delta_ishikawa_2026-09.md`. No new M3 theorem should
be started merely because it is mathematically available.

## 8. Candidate B application status

The integration precheck in `docs/m3_canonical_integration_precheck.md`
independently reconstructed the Candidate B artifact audit:

- the 16 block-aligned residual comparisons were reconstructed;
- the fully active bundled and split cases are UNSAT;
- the 15 proper bundled residuals are SAT;
- five split singleton repairs are SAT;
- the grouped family is `{asymm}`, `{un}`, `{minlib}`, `{no_cycle4}`.

PR #18 added a canonical deterministic checker and anonymous-supplement builder
for the narrower M1.5 C1-C5 witness claims, together with exact hashes in
`papers/m1_5/CLAIM_BOUNDARY.md`.

The full Candidate B M3 application is now separately frozen under
`m3/candidate_b/` at evidence-freeze commit
`99cba5cd45cadab283aab3784c9ff2180c8d8609`. The whitelist-only package binds
99 tracked source-evidence files to the exact historical source provenance,
while its default curated rebuild requires no off-main Git object. It
independently recomputes the 16-row ResidualFaithfulness table, the complete
16/32 deletion lattices and repair families, direct GroupSoundness, bundled deletion
monotonicity, and pointwise grouped correctness. All 15 required fault
injections fail at their expected gates. A separate deterministic anonymous
builder sanitizes and rehashes its review archive.

Candidate B is artifact-defined. Its evidence remains outside the M3 Lean
theorem core, and the package does not establish semantic atom validity,
encoder or solver correctness, proof replay, normative grouping, or
family-scale transfer. No tag or public release has been created; release is
gated by license and redistribution review.

Candidate B has a canonical validator-backed evidence package on `main`;
immutable release binding and redistribution review remain pending. The main
integration commit is `abec37c61a7c1217d8debf76b31366f1ff02e57f`. It does
not establish semantic contract validity, encoder correctness, Candidate B
formalization in Lean, solver/proof replay, normative optimality, or
family-scale validity.

## 9. CPP integrated manuscript status

PR #19 added `papers/cpp2027_m1_5_m3/` as the canonical workspace for the
integrated M1.5+M3 CPP 2027 v1 working draft. Its evidence layers remain
separate:

- the Section 3 concrete no-go witness is artifact-checked through the M1.5
  C1-C5 binding;
- the abstract finite-set characterization is Lean-kernel checked under
  `SocialChoiceAtlas/Reportability/`;
- the concrete grouped reading is artifact-level and is not a Lean theorem.

The workspace has passed its recorded G2 draft-integration checks. No inspected
GitHub state establishes acceptance, final submission readiness, a submission
tag, or a public artifact release.

## 10. Dafny workflow pilot status

The public `SHayashida/dafny-m3-repair` repository contains one
hand-constructed minimum example at commit
`208c2a59aa24fc1d2befe22842a7b07af8ced576`. It records a failing
caller/callee precondition mismatch and three distinct repair directions:

- strengthen the caller contract, with an explicit upstream obligation
  propagation example;
- weaken the callee contract while preserving the recorded existing client;
- change the implementation while preserving the public contracts.

The pilot addresses the following workflow questions rather than proving a
general theorem:

- whether fixing the repair atoms or scope in advance can exclude otherwise
  relevant candidates;
- which role consumes candidates, including a repair-tool author, verification
  engineer, or specification/API owner;
- whether technical verifier success and specification-revision acceptance
  require different reporting contracts;
- how multiple cases and a real formal-model-repair workflow could provide
  evidence beyond a hand-constructed example.

At present this is a minimum example only. Automatic candidate generation,
multiple case studies, real-workflow validation, prevalence, and generality are
not verified. The pilot does not validate M3 generally and does not establish
that pre-atomicization can never prevent the reportability problem.

## 11. Publication-unit status

- M2 standalone publication decision is `CONDITIONAL GO`; required major
  manuscript revision remains before submission.
- M1.5 and M3 form the current integrated CPP 2027 working-draft unit under
  `papers/cpp2027_m1_5_m3/`.
- The current theorem and research claim boundary are frozen; submission
  preparation and artifact release remain separate decisions.
- No separate canonical `papers/m3/` workspace exists; the integrated workspace
  is the current manuscript unit.
- `papers/m4/` is a repository-local RC preprint workspace for claim-boundary
  review, not a public release.
- M2.1 remains separate and deferred.
- The XAI companion remains deferred or parallel; no public artifact status is
  inferred here.
- Publication packaging does not establish doctoral enrollment or an accepted
  doctoral plan.

## 12. Active next actions

1. Decide whether to hold the frozen M1.5+M3 unit for doctoral publication
   timing or prepare it for submission without broadening its claim boundary.
2. Review the frozen Candidate B package for a future immutable release only
   after license and redistribution gates pass.
3. Keep any Dafny multi-case or real-workflow extension as separate follow-up
   evidence, not as a blocker or theorem premise for the current paper.
4. Complete the required M2 manuscript revision before submission.
5. Keep the XAI companion deferred or parallel until its public status is
   explicit.
6. Keep M4 institutional-warrant work future/deferred from the immediate
   publication track.
7. Defer M2.1 paper integration and maintenance cleanup.

Peer-reviewed publication of the integrated M1.5+M3 unit is the immediate
objective. The program may serve as a potential doctoral research spine, but no
doctoral enrollment or accepted plan is claimed.

## 13. Non-blocking backlog

- M3 linter-warning cleanup, only in a separately audited code task.
- Stale M3 skeleton retention/archival policy.
- Candidate B license, redistribution, and immutable-release review; the
  clean-clone dependency gate is complete.
- Dafny multi-case and real-workflow validation.
- M2 manuscript major revision.
- M2.1 publication packaging.
- XAI companion only after an explicit public-status decision.
- M4 institutional-warrant theory and any future publication unit.
- Legacy M2 helper cleanup.
- macOS portability maintenance.
- Optional full-asset Zenodo enrichment.
- Historical branch cleanup only after archival review.

## 14. Source-of-truth hierarchy

1. Paper-specific claim-boundary files govern individual paper claims.
2. `docs/doctoral_scope_lock.md` governs the potential doctoral-scope candidate
   boundaries; it is not evidence of enrollment, supervision, or plan approval.
3. `docs/research_program_current.md` governs current program status.
4. `RESEARCH_STATUS.md` is a concise operational summary.
5. `README.md` is a public overview and does not broaden any claim.

Where the scope-lock document contains a historical progress snapshot, this
file governs current milestone status; routine status synchronization does not
amend the locked scope decision.
