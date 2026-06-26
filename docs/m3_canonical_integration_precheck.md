# M3 Canonical Integration Precheck

## 1. Precheck identity

This document is a read-only canonical-integration precheck for the off-main M3
reportability development.

Repository:

```text
SHayashida/Sen-Lean4
```

Canonical branch:

```text
main
```

Precheck branch:

```text
codex/m3-canonical-integration-precheck
```

Audited M3 source branch:

```text
origin/codex/m3-lean-reportability
```

This precheck does not merge, cherry-pick, rebase, rewrite, or otherwise modify
the M3 source branch. It does not integrate M3 code or artifacts. The only
permanent repository change made by this task is this file.

## 2. Canonical main and source-branch provenance

Remote provenance was fetched with tags before the audit and again before
writing this report.

| Item | Actual value |
| --- | --- |
| `origin/main` | `457713e355686f0cc199525c1c0b47293a173193` |
| `origin/codex/m3-lean-reportability` before audit | `1c2b9e7b979ba1a4b08c1d69f5400907cf2ca689` |
| `origin/codex/m3-lean-reportability` at report creation | `1c2b9e7b979ba1a4b08c1d69f5400907cf2ca689` |
| Merge base | `73c891fa3edd96148238570f16453c484fccf283` |
| Divergence | `origin/main` has 21 unique commits; M3 source has 20 unique commits |
| Open PRs at initial audit | `[]` |
| Canonical M2 tag | `papers-m2-v2-obstruction-bridge` |
| Canonical M2 archived commit | `d7e5fd1ac94ab18330951b5d9741585dddc5b43a` |
| M2 archived commit ancestor of `origin/main` | yes |
| M2 tag target | `d7e5fd1ac94ab18330951b5d9741585dddc5b43a` |

The source branch was treated as immutable. All source-head and synthetic
integration checks used detached worktrees under `/tmp`.

## 3. Divergence and commit inventory

The source branch has 20 commits not on current `origin/main`. The full commit
table is in Appendix A.

Summary:

| Category | Commits | Cherry-pick status |
| --- | ---: | --- |
| `M3_CORE` | 0 pure commits | The Lean core is present, but its commit is mixed with root import glue |
| `M3_CURRENT_DOC` | 3 pure commits | Eligible only after document freshness review |
| `M3_STALE_SCAFFOLD` | 8 pure commits | Do not cherry-pick as canonical docs |
| `M3_CANDIDATE_B_AUDIT` | 3 pure commits | Eligible only with evidence binding |
| `CANDIDATE_B_EVIDENCE` | 0 pure commits | Evidence is mixed with `.gitignore` and repair-liftability results |
| `M2_1` | 1 pure commit | Exclude from M3 integration |
| `ARROW_EXCLUDED` | 1 pure commit | Exclude from doctoral M3 integration |
| `MIXED` | 4 commits | Do not cherry-pick |

Commit purity conclusion:

- No M3 theorem-core commit should be cherry-picked directly.
- The theorem core should be cleanly extracted by file from the exact source
  SHA `1c2b9e7b979ba1a4b08c1d69f5400907cf2ca689`.
- Mixed commits must not be cherry-picked because they combine root glue,
  stale docs, evidence trees, M2.1 material, or unrelated result trees.

## 4. File and subtree inventory

Branch-only diff from the merge base:

```text
254 files changed, 28059 insertions(+), 5 deletions(-)
```

Top-level changed units:

| Path or subtree | Status | Files | Disposition |
| --- | --- | ---: | --- |
| `.gitignore` | modified | 1 | `EXCLUDE_STALE_GLUE` |
| `SocialChoiceAtlas.lean` | modified | 1 | patch current `main`, do not copy source file |
| `SocialChoiceAtlas/Reportability/**` | added | 5 | `INTEGRATE_UNCHANGED` for PR-M3-CORE |
| `docs/m1_5_to_m3_transition.md` | added | 1 | `INTEGRATE_AFTER_REVISION` |
| `docs/m2b_arrow_transfer_prerequisites.md` | added | 1 | `EXCLUDE_DOCTORAL_SCOPE` |
| `docs/m3_atomicity_theorem_skeleton.md` | added | 1 | `HISTORICAL_OFF_MAIN` |
| `docs/m3_candidate_b_group_soundness_audit_plan.md` | added | 1 | `INTEGRATE_ONLY_WITH_EVIDENCE` or supersede |
| `docs/m3_candidate_b_group_soundness_audit_result.md` | added | 1 | `INTEGRATE_ONLY_WITH_EVIDENCE` |
| `docs/m3_nonatomic_group_soundness_skeleton.md` | added | 1 | `HISTORICAL_OFF_MAIN` |
| `docs/m3_paper_section_allocation.md` | added | 1 | `HISTORICAL_OFF_MAIN` |
| `docs/m3_reportability_contract.md` | added | 1 | `INTEGRATE_AFTER_REVISION` |
| `papers/m2_1/**` | added | 13 | `EXCLUDE_M2_1` |
| `results/20260401/candidate_b_minlib_granularity/**` | added | 197 | `INTEGRATE_ONLY_WITH_EVIDENCE` |
| `results/20260401/repair_liftability/**` | added | 29 | `EXCLUDE_UNRELATED_RESULTS` |

Result subtree audit:

| Tree | Files | Bytes | Extensions | Zero-byte | Malformed JSON | LFS pointers | Symlinks | Largest files | Completeness |
| --- | ---: | ---: | --- | ---: | ---: | ---: | ---: | --- | --- |
| `results/20260401/candidate_b_minlib_granularity/**` | 197 | 327877 | `.csv`: 1, `.json`: 195, `.md`: 1 | 0 | 0 | 0 | 0 | `split/atlas.json` 68605 bytes; `bundled/atlas.json` 32065 bytes; `comparison.json` 27937 bytes | complete for the audited Candidate B claims |
| `results/20260401/repair_liftability/**` | 29 | 128476 | `.csv`: 3, `.json`: 23, `.md`: 3 | 0 | 0 | 0 | 0 | `liftability_step3.json` 37055 bytes; `liftability_step2.json` 22764 bytes | complete as a tree, but unrelated to M3 theorem-core integration |
| `results/20260401/**` total | 226 | 456353 | `.csv`: 4, `.json`: 218, `.md`: 4 | 0 | 0 | 0 | 0 | see above | mixed evidence/results tree |

## 5. Classification matrix

| Unit | Classification | Reason |
| --- | --- | --- |
| `SocialChoiceAtlas/Reportability/Defs.lean` | `INTEGRATE_UNCHANGED` | Pure finite-set definitions; builds against source and current `main` |
| `SocialChoiceAtlas/Reportability/Atomic.lean` | `INTEGRATE_UNCHANGED` | M3-A theorem core; builds unchanged |
| `SocialChoiceAtlas/Reportability/GroupSound.lean` | `INTEGRATE_UNCHANGED` | M3-B theorem core; builds unchanged |
| `SocialChoiceAtlas/Reportability/Monotone.lean` | `INTEGRATE_UNCHANGED` | M3-C converse, exactness, hierarchy; builds unchanged |
| `SocialChoiceAtlas/Reportability/Examples.lean` | `INTEGRATE_UNCHANGED` | Finite boundary examples; builds unchanged |
| Source `SocialChoiceAtlas.lean` | `EXCLUDE_STALE_GLUE` | Drops current `main`'s `ObstructionBridge` import and rewrites M2 framing |
| Current `SocialChoiceAtlas.lean` patched with five imports | `INTEGRATE_AFTER_REVISION` | Synthetic integration succeeds with patch-only import addition |
| Source `.gitignore` | `EXCLUDE_STALE_GLUE` | Broad result/PDF ignore policy changes are not needed for M3 theorem core |
| Candidate B evidence tree | `INTEGRATE_ONLY_WITH_EVIDENCE` | Complete off-main evidence exists, but needs curated package or release binding |
| Candidate B audit result | `INTEGRATE_ONLY_WITH_EVIDENCE` | Valid only if cited paths are canonical or immutable |
| Arrow prerequisites doc | `EXCLUDE_DOCTORAL_SCOPE` | Arrow is explicitly outside doctoral completion scope |
| M2.1 manuscript subtree | `EXCLUDE_M2_1` | Separate publication unit; not part of M3 core |
| Repair-liftability result tree | `EXCLUDE_UNRELATED_RESULTS` | Not required for M3 theorem core or Candidate B M3-B instantiation |

## 6. M3 public API inventory

The M3 Lean public API is explicit and finite-set based. It does not formalize
CNF, SAT solving, LRAT, or Candidate B artifacts.

Core definitions:

| Declaration | Role |
| --- | --- |
| `betaSet` | Block image of a finite set of contract atoms |
| `LambdaI` | Active implementation interface induced by active atoms |
| `InclusionMinimal` | Local subset-minimality predicate |
| `BlocksDisjoint` | Pairwise disjoint active implementation blocks |
| `BlocksNonempty` | Nonempty active implementation blocks |
| `RawFeasible` | Implementation deletion feasibility using retained levers |
| `RawRepair` | Inclusion-minimal feasible implementation deletion |
| `groupTouchAny` | Touch-any grouping from lever deletions to atom deletions |
| `ContractFeasible` | Contract deletion feasibility using retained atoms |
| `ContractRepair` | Inclusion-minimal feasible contract deletion |
| `IsRawGroup` | Grouped image of a raw repair |
| `GroupedRepair` | Inclusion-minimal element of the grouped raw image |
| `ResidualFaithfulness` | Agreement on block-aligned retained residuals |
| `RepairAtomicity` | Every active atom has a singleton block |
| `GroupSoundness` | Arbitrary feasible implementation deletions remain feasible after grouping |
| `PsiDeletionMonotonicity` | Reference retained-set feasibility is monotone downward under further deletion |

Main theorem declarations:

| Declaration | Role |
| --- | --- |
| `m3a_grouped_correctness` | M3-A atomic grouped correctness |
| `m3a_raw_transport` | M3-A atom-indexed raw transport |
| `m3b_grouped_correctness` | M3-B non-atomic grouped correctness |
| `m3b_two_realization` | M3-B two-realization grouped invariance |
| `audit_cost_collapse` | Reduces unrestricted `GroupSoundness` audit to raw repairs under `PsiDeletionMonotonicity` |
| `m3c_converse` | M3-C converse without `ResidualFaithfulness` |
| `groupSoundness_iff` | M3-B/C exactness under faithfulness and reference monotonicity |
| `atomicity_implies_groupSoundness` | M3-A hierarchy lemma |

Verified semantic/API points:

1. `ResidualFaithfulness` quantifies only over `T ⊆ I` and compares
   `SatPhi (betaSet beta T)` with `SatPsi T`.
2. `GroupSoundness` quantifies over arbitrary `R ⊆ LambdaI I beta`.
3. `GroupedRepair` minimizes `IsRawGroup`, the grouped raw image.
4. `groupTouchAny` reports atom `a` exactly when `R ∩ beta a` is nonempty.
5. Inactive atoms are excluded by filtering over `I`.
6. `InclusionMinimal P X` uses `P X ∧ ∀ Y, P Y → Y ⊆ X → X ⊆ Y`.
7. Retained-set complements are used consistently as `LambdaI I beta \ R` and
   `I \ G`.
8. M3-A raw transport is atom-indexed and requires atomicity on both
   realizations.
9. M3-B does not claim raw transport.
10. M3-C uses `PsiDeletionMonotonicity` in the retained-set downward direction.
11. `groupSoundness_iff` requires `BlocksDisjoint`, `ResidualFaithfulness`, and
    `PsiDeletionMonotonicity`.
12. Fully active UNSAT is application-side and is not a theorem hypothesis.

## 7. Assumption matrix

| Theorem | Disjointness | Atomicity | Faithfulness | GroupSoundness | Psi monotonicity | Fully active UNSAT | Conclusion |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | --- |
| `m3a_grouped_correctness` | yes | yes | yes | no | no | no | `∀ G, GroupedRepair I beta SatPhi G ↔ ContractRepair I SatPsi G` |
| `m3a_raw_transport` | yes, both realizations | yes, both realizations | yes, both realizations | no | no | no | `RawRepair` transports between atom-indexed block deletions |
| `m3b_grouped_correctness` | yes | no | yes | yes | no | no | pointwise grouped correctness |
| `m3b_two_realization` | yes, both realizations | no | yes, both realizations | yes, both realizations | no | no | two grouped predicates are pointwise equivalent |
| `audit_cost_collapse` | no | no | no | raw-repair checks only | yes | no | unrestricted `GroupSoundness` |
| `m3c_converse` | no | no | no | no | yes | no | grouped correctness implies `GroupSoundness` |
| `groupSoundness_iff` | yes | no | yes | conclusion side | yes | no | `GroupSoundness ↔` grouped correctness |
| `atomicity_implies_groupSoundness` | yes | yes | yes | conclusion | no | no | M3-A condition implies M3-B condition |

No theorem in the M3 core assumes deletion monotonicity of `SatPhi`.

## 8. Source-head build and axiom audit

Source worktree:

```text
/tmp/.../m3-source
```

Source head:

```text
1c2b9e7b979ba1a4b08c1d69f5400907cf2ca689
```

Source-head checks:

| Check | Result |
| --- | --- |
| `git status --short` | clean before temporary audit files |
| `lake env lean SocialChoiceAtlas/Reportability/Defs.lean` | pass with non-fatal linter warnings |
| `lake env lean SocialChoiceAtlas/Reportability/Atomic.lean` | pass with non-fatal linter warnings |
| `lake env lean SocialChoiceAtlas/Reportability/GroupSound.lean` | pass |
| `lake env lean SocialChoiceAtlas/Reportability/Monotone.lean` | pass |
| `lake env lean SocialChoiceAtlas/Reportability/Examples.lean` | pass with one non-fatal `unnecessarySimpa` warning |
| `lake build` | pass |
| `git diff --check` | pass |

Warnings:

- `Defs.lean`: four unused-section-variable linter warnings.
- `Atomic.lean`: two unused-section-variable linter warnings.
- `Examples.lean`: one `try 'simp' instead of 'simpa'` linter warning.
- Existing `BaseCase24/Theorem.lean` linter warnings also appear in full
  source builds.

Unfinished proof marker search:

```text
grep -RInE '\bsorry\b|\badmit\b|aesop\?|exact\?|by_contra\?' SocialChoiceAtlas/Reportability
```

Result:

```text
no hits
```

Broad dependency and shortcut search:

```text
grep -RIn 'native_decide\|Classical\|axiom\|unsafe\|noncomputable' SocialChoiceAtlas/Reportability
```

Result:

- `native_decide` appears only in `SocialChoiceAtlas/Reportability/Examples.lean`.
- Classification: boundary examples.
- No `Classical`, `axiom`, `unsafe`, or `noncomputable` hits in the
  Reportability directory.

Axiom audit:

| Declaration | Axioms reported by Lean |
| --- | --- |
| `m3a_grouped_correctness` | `[propext, Classical.choice, Quot.sound]` |
| `m3a_raw_transport` | `[propext, Classical.choice, Quot.sound]` |
| `m3b_grouped_correctness` | `[propext, Classical.choice, Quot.sound]` |
| `m3b_two_realization` | `[propext, Classical.choice, Quot.sound]` |
| `audit_cost_collapse` | `[propext, Classical.choice, Quot.sound]` |
| `m3c_converse` | `[propext, Classical.choice, Quot.sound]` |
| `groupSoundness_iff` | `[propext, Classical.choice, Quot.sound]` |
| `atomicity_implies_groupSoundness` | `[propext, Classical.choice, Quot.sound]` |

No unexpected custom axiom was found.

## 9. Adversarial theorem-core audit T1-T15

| Attack | Result | Finding |
| --- | --- | --- |
| T1 Circularity | PASS | `GroupSoundness` is per-deletion feasibility over arbitrary implementation deletions; grouped correctness is a minimal-report equality. M3-B is not a tautological restatement. |
| T2 Faithfulness strength | PASS | `ResidualFaithfulness` is limited to block-aligned retained residuals. It does not itself control arbitrary partial deletions. |
| T3 Touch-any policy dependence | PASS | Theorems are contract-relative to `groupTouchAny`; all-touch, threshold, or role-sensitive grouping would require new definitions and proofs. |
| T4 Atomicity role | PASS | Atomicity is used to align arbitrary lever deletions with atom sets and in `atomicity_implies_groupSoundness`; complement and block-image grouping identities do not need atomicity. |
| T5 Finite descent | PASS | Minimal-subset existence uses finite descent over `Finset` subsets and no `SatPhi` monotonicity. |
| T6 Empty and degenerate cases | MINOR | Empty active sets and already-SAT top residuals are mathematically allowed. The impossibility-repair reading requires application-side fully active UNSAT. |
| T7 Minimality transport | PASS | `rawRepair_betaSet_iff_contractRepair` proves both directions under disjointness, atomicity, faithfulness, and `G ⊆ I`. |
| T8 Raw transport | PASS | `m3a_raw_transport` transports raw repairs for atom-indexed block deletions across two atomic realizations; it is stronger than equality after grouping. |
| T9 M3-B completeness | PASS | `contractRepair_isRawGroup` and `groupedRepair_iff_contractRepair` prove representation of every contract repair and correctness of every minimal grouped image. |
| T10 M3-C converse | PASS | `m3c_converse` uses only grouped correctness and `PsiDeletionMonotonicity`; `ResidualFaithfulness` is absent. |
| T11 Monotonicity necessity | PASS | `Examples.NonMonotone` proves grouped correctness, failed `GroupSoundness`, and failed `PsiDeletionMonotonicity`. |
| T12 Atomicity non-necessity | PASS | `Examples.NonAtomic` proves failed `RepairAtomicity`, `ResidualFaithfulness`, and `GroupSoundness`. |
| T13 Implementation monotonicity | PASS | No theorem assumes deletion monotonicity of `SatPhi`. |
| T14 Candidate B separation | PASS | Lean modules and examples state that Candidate B artifacts are not formalized. |
| T15 Claim boundary | PASS | The theorem core proves reportability relative to abstract predicates, not semantic validity of social-choice atoms. |

No blocking theorem-core issue was found.

## 10. Synthetic integration against current main

Synthetic worktree:

```text
/tmp/.../m3-integration-simulation
```

Base:

```text
origin/main at 457713e355686f0cc199525c1c0b47293a173193
```

Synthetic integration action:

1. Restored only `SocialChoiceAtlas/Reportability/**` from
   `origin/codex/m3-lean-reportability`.
2. Patched only the temporary `SocialChoiceAtlas.lean` with five imports:

```lean
import SocialChoiceAtlas.Reportability.Defs
import SocialChoiceAtlas.Reportability.Atomic
import SocialChoiceAtlas.Reportability.GroupSound
import SocialChoiceAtlas.Reportability.Monotone
import SocialChoiceAtlas.Reportability.Examples
```

3. Preserved current `main` imports:

```lean
import SocialChoiceAtlas.Sen.ObstructionBridge
import SocialChoiceAtlas.Sen.Lifting.ImpossibilityLift
```

Synthetic checks:

| Check | Result |
| --- | --- |
| Five Reportability module builds | pass |
| Five direct `lake env lean` checks after module compilation | pass |
| `./scripts/ci_m2_smoke.sh` | pass |
| `lake build` | pass |
| `git diff --check` | pass |

Temporary diff:

```text
SocialChoiceAtlas.lean | 5 +++++
SocialChoiceAtlas/Reportability/** | added in detached worktree only
```

The five M3 Lean files build unchanged against current `main`. The root import
change is additive when applied to current `main`; copying the source-branch
root file would be unsafe.

## 11. Root-import and integration-glue decision

| Path | Copy whole file? | Patch current main? | Exclude? | Reason |
| --- | ---: | ---: | ---: | --- |
| `SocialChoiceAtlas.lean` | no | yes | source file yes | Source file drops `ObstructionBridge` and uses stale M2 comment; synthetic patch of five imports succeeds |
| `.gitignore` | no | no | yes | Source changes broaden result/PDF ignore behavior and are not required for theorem core |

Future PR-M3-CORE should patch current `main`'s `SocialChoiceAtlas.lean` with
the five Reportability imports and preserve the M2 obstruction-bridge imports
and comments.

## 12. Documentation freshness audit

| Document | Purpose | Claim status | Lean correspondence | Stale or scope issue | Disposition |
| --- | --- | --- | --- | --- | --- |
| `docs/m1_5_to_m3_transition.md` | Dissertation-spine transition from M1.5 to M3 | Mostly current | Names all new Lean declarations | Off-main source text should be checked against current scope lock and integrated only after M3 core is canonical | `REVISE_THEN_INTEGRATE` |
| `docs/m2b_arrow_transfer_prerequisites.md` | Arrow prerequisite/scope planning | Future-work only | No M3 Lean dependency | Arrow is excluded from doctoral completion by `docs/doctoral_scope_lock.md` | `KEEP_OFF_MAIN` |
| `docs/m3_atomicity_theorem_skeleton.md` | Proof skeleton for M3-A | Historical scaffold | Superseded by `Atomic.lean` | Assumes fully active UNSAT in theorem narrative although Lean keeps it application-side | `INTEGRATE_AS_HISTORICAL` or keep off-main; not canonical theorem doc |
| `docs/m3_candidate_b_group_soundness_audit_plan.md` | Artifact-only Candidate B audit plan | Useful provenance | Not Lean-formalized | Depends on off-main result paths | `REVISE_THEN_INTEGRATE` only with evidence package |
| `docs/m3_candidate_b_group_soundness_audit_result.md` | Candidate B audit result | Artifact-backed PASS | Uses M3-B concepts, not Lean artifact formalization | Must not be integrated unless cited evidence is canonical or immutable | `REVISE_THEN_INTEGRATE` only with evidence package |
| `docs/m3_nonatomic_group_soundness_skeleton.md` | M3-B/M3-C skeleton | Historical scaffold | Superseded by `GroupSound.lean` and `Monotone.lean` | Calls M3-C candidate/pending in places | `INTEGRATE_AS_HISTORICAL` or keep off-main; not current canonical doc |
| `docs/m3_paper_section_allocation.md` | Planning allocation | Stale | Says formalization pending and M3-C promotion pending | Conflicts with completed Lean core | `KEEP_OFF_MAIN` |
| `docs/m3_reportability_contract.md` | Contract definitions and framing | Needs revision | Matches some definitions but foregrounds atomicity as main target | Completion criteria mention Arrow; not compatible with scope lock if read as requirement | `REVISE_THEN_INTEGRATE` |

Mandatory freshness findings:

- `m3_reportability_contract.md` still foregrounds "lever atomicity suffices"
  as the main theorem target. It should be revised to present the M3-A/B/C
  hierarchy before canonical integration.
- Any Arrow completion criterion must be removed or explicitly marked as
  non-doctoral future work.
- `m3_paper_section_allocation.md` contains stale "formalization pending" and
  "candidate theorem" statuses after the Lean implementation.
- Skeleton documents should not be placed on `main` as current theorem docs.
  Git history already preserves them.
- Candidate B audit docs require evidence binding before integration.

## 13. Candidate B independent evidence audit

Primary artifact tree:

```text
results/20260401/candidate_b_minlib_granularity/**
```

Artifacts inspected:

- `comparison.json`
- `comparison.csv`
- `bundled/atlas.json`
- `split/atlas.json`
- `summary.md`
- `bundled/case_11101/summary.json`
- `split/case_111101/summary.json`
- all case summaries required for the 16 no-cycle3-off block-aligned rows
- split singleton deletion summaries for `case_011101`, `case_101101`,
  `case_110101`, `case_111001`, and `case_111100`
- adjacent manifests for hash cross-checks

Independent reconstruction results:

| Claim | Result | Evidence |
| --- | --- | --- |
| JSON parse validity | PASS | 195 Candidate B JSON files parsed; 0 malformed |
| Bundled universe | PASS | `comparison.json`: `[asymm, un, minlib, no_cycle3, no_cycle4]` |
| Split universe | PASS | `comparison.json`: `[asymm, un, decisive_voter0, decisive_voter1, no_cycle3, no_cycle4]` |
| Contract active atoms | PASS | `I = {asymm, un, minlib, no_cycle4}` with `no_cycle3 = off` |
| 16 block-aligned rows exist | PASS | all 16 rows present in `mapped_cases` |
| `no_cycle3` off in audited rows | PASS | bundled bit 4 and split bit 5 are `0` in all 16 rows |
| Status matches in all 16 rows | PASS | every audited row has equal bundled/split SAT status |
| Clause multiset equality in all 16 rows | PASS | every audited row has `clause_multiset_equal = true` |
| Fully active bundled residual | PASS | `bundled/case_11101` is `UNSAT` |
| Fully active split residual | PASS | `split/case_111101` is `UNSAT` |
| Proper bundled subsets | PASS | all 15 proper rows in the contract lattice are `SAT` |
| Split singleton deletions | PASS | all five singleton retained cases are `SAT` |
| Split active interface size | PASS | five active levers after excluding `no_cycle3` |
| RawRep completeness | PASS | full active split is `UNSAT`; all singleton deletions are `SAT`; larger deletions contain singleton repairs |
| Grouped singleton family | PASS | `{asymm}`, `{un}`, `{minlib}`, `{no_cycle4}` |
| `PsiDeletionMonotonicity` | PASS | no violations over the 16-row bundled lattice |
| CSV/JSON/atlas consistency | PASS with note | `comparison.csv` cross-checks the two repair witnesses only; full status lattice is in JSON/atlases |
| Cited case files | PASS | all cited summaries exist and are nonempty |
| Manifest hash consistency | PASS | case summary `cnf_sha256` values match adjacent `sen24.manifest.json` values |

Important evidence caveat:

The Candidate B artifacts are complete on the source branch, but they are not
canonical on `main`. The Candidate B application claim should not be integrated
without either a curated evidence package, the full evidence tree, or an
immutable release binding.

## 14. Evidence dependency graph

Dependency graph for the Candidate B M3-B claim:

```text
M3 prose claim:
  Candidate B instantiates M3-B under an artifact-defined bundled contract
→ audit inference:
  ResidualFaithfulness + GroupSoundness + PsiDeletionMonotonicity + RawRep completeness
→ source JSON/CSV row:
  comparison.json mapped_cases; comparison.csv repair witness rows
→ case summary or manifest:
  bundled/split atlas cases, cited summary.json files, sen24.manifest.json hashes
→ generator / validator path:
  scripts/gen_dimacs.py has canonical decisive_voter selector support;
  no dedicated canonical M3 Candidate B validator currently exists
→ immutable commit or release identity:
  off-main mutable branch head `1c2b9e7b979ba1a4b08c1d69f5400907cf2ca689`;
  no tag, release, checksum manifest, or DOI binding yet
```

Dependency status:

| Dependency | Status |
| --- | --- |
| M3 theorem core | off-main but builds cleanly |
| Candidate B output files | off-main but complete |
| Candidate B audit docs | off-main and path-dependent |
| Generator support for decisive-voter selectors | canonical on `main` via `scripts/gen_dimacs.py` |
| Independent Candidate B M3 validator | missing |
| Immutable release binding | missing |

The evidence supports the claim inside the source branch, but the path binding
is not yet stable enough for canonical `main`.

## 15. Minimum closed evidence set

Candidate packaging options:

| Option | Independent auditability | Reproducibility | Repository size discipline | Provenance stability | Reviewer usability | Maintenance cost | Broken-path risk | Total | Assessment |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | --- |
| E1 full evidence tree | 5 | 4 | 2 | 4 | 4 | 2 | 3 | 24 | viable but pulls 197 files |
| E2 curated evidence package | 5 | 4 | 5 | 4 | 5 | 4 | 4 | 31 | best primary option |
| E3 immutable release binding | 4 | 5 | 5 | 5 | 3 | 4 | 4 | 30 | best fallback |
| E4 defer Candidate B | 1 | 3 | 5 | 5 | 2 | 5 | 5 | 26 | safe but loses application claim |

Primary recommendation:

```text
E2. Curated evidence package
```

Fallback recommendation:

```text
E3. Immutable release binding
```

Minimum curated evidence package:

| File or selection rule | Classification | Reason |
| --- | --- | --- |
| `results/20260401/candidate_b_minlib_granularity/comparison.json` | REQUIRED | ordered universes, 32 mapped cases, status equality, clause-multiset equality |
| `results/20260401/candidate_b_minlib_granularity/comparison.csv` | REDUNDANT_CROSSCHECK | two repair witness rows |
| `results/20260401/candidate_b_minlib_granularity/summary.md` | PROVENANCE_ONLY | human-readable overview |
| `results/20260401/candidate_b_minlib_granularity/bundled/atlas.json` | REQUIRED | complete 32-case bundled status atlas |
| `results/20260401/candidate_b_minlib_granularity/split/atlas.json` | REQUIRED | complete 64-case split status atlas |
| `bundled/case_<bid>/summary.json` for the 16 no-cycle3-off bundled case ids in Appendix C | REQUIRED | direct case-level evidence |
| `split/case_<sid>/summary.json` for the 16 mapped split case ids in Appendix C | REQUIRED | direct case-level evidence |
| `split/case_110101/summary.json` and `split/case_111001/summary.json` | REQUIRED | non-block-aligned singleton repairs for `decisive_voter0` and `decisive_voter1` |
| Adjacent `sen24.manifest.json` for every cited case directory | REQUIRED | CNF hash and clause-category provenance |
| `scripts/validate_m3_candidate_b_evidence.py` | REQUIRED new validator | independent artifact-only validator; should be added in PR-M3-EVIDENCE |
| Raw CNF, solver logs, and proof logs | NOT_NEEDED for curated audit | the current M3 application audit reads status summaries and manifests only |

## 16. Explicit exclusions

| Excluded unit | Scientific reason | Repository-governance reason | Future separate task? |
| --- | --- | --- | --- |
| `papers/m2_1/**` | M2.1 is a companion boundary study, not M3 theorem core | Avoid mixing publication units | yes |
| `results/20260401/repair_liftability/**` | Not used by M3-A/B/C or Candidate B M3-B instantiation | Avoid unrelated result-tree integration | yes, if a separate paper needs it |
| `docs/m2b_arrow_transfer_prerequisites.md` | Arrow is a future truth/certificate prerequisite testbed, not an M3 application in doctoral scope | `docs/doctoral_scope_lock.md` excludes Arrow as a completion requirement | yes, as future work |
| Source-branch `.gitignore` | Not scientifically relevant to M3 core | Broad ignore-policy changes require separate review | yes, if independently justified |
| Source-branch `SocialChoiceAtlas.lean` as a whole file | It omits current `main`'s `ObstructionBridge` import | Copying it would regress current M2 root imports | no; patch current main instead |

## 17. Integration-history decision

| Strategy | Decision | Reason |
| --- | --- | --- |
| Whole branch merge | prohibited | Branch mixes M3 Lean core, stale scaffolding docs, Candidate B evidence, M2.1 manuscript, Arrow planning, repair-liftability results, and stale glue |
| Selected commit cherry-pick | not primary | M3 core commit is mixed with root import glue; evidence commit is mixed with unrelated results |
| Clean file extraction from exact source SHA | primary for PR-M3-CORE | Builds against current `main`; avoids mixed history |
| Manual reimplementation | not needed | No blocking theorem-core defect was found |

Primary PR-M3-CORE strategy:

```text
Clean file extraction from source SHA 1c2b9e7b979ba1a4b08c1d69f5400907cf2ca689,
plus patch-only root imports on current main.
```

## 18. Exact PR-M3-CORE manifest

Required paths:

```text
SocialChoiceAtlas/Reportability/Defs.lean
SocialChoiceAtlas/Reportability/Atomic.lean
SocialChoiceAtlas/Reportability/GroupSound.lean
SocialChoiceAtlas/Reportability/Monotone.lean
SocialChoiceAtlas/Reportability/Examples.lean
SocialChoiceAtlas.lean                    patch only
```

Recommended but not required:

```text
scripts/ci_m3_smoke.sh
```

If added, the smoke gate should build only the five Reportability modules and
run the axiom audit commands. It should not run solvers.

Proposed logical commits:

```text
feat(m3): add finite-set reportability definitions
feat(m3): prove atomic and group-sound reportability
feat(m3): prove monotone exactness and boundary examples
test(m3): add focused reportability smoke gate
```

Do not include:

```text
.gitignore
docs/**
papers/**
results/**
```

in PR-M3-CORE.

## 19. Exact PR-M3-DOCS manifest

Revise and integrate after PR-M3-CORE:

```text
docs/m3_reportability_contract.md
docs/m1_5_to_m3_transition.md
```

Integrate only with evidence package or release binding:

```text
docs/m3_candidate_b_group_soundness_audit_plan.md
docs/m3_candidate_b_group_soundness_audit_result.md
```

Keep off-main or historical unless explicitly requested:

```text
docs/m3_atomicity_theorem_skeleton.md
docs/m3_nonatomic_group_soundness_skeleton.md
docs/m3_paper_section_allocation.md
docs/m2b_arrow_transfer_prerequisites.md
```

Required doc revisions before integration:

- Remove or qualify stale "formalization pending" language.
- Promote M3-C only according to the actual Lean theorem status.
- Present M3-A/B/C as the hierarchy, not atomicity alone.
- Remove any Arrow completion requirement from the doctoral M3 path.
- Preserve the artifact-defined versus semantic/Lean-level contract distinction.

## 20. Exact PR-M3-EVIDENCE manifest

Primary path:

```text
Curated evidence package under a reviewed results path, plus validator.
```

Exact required files or rules:

```text
results/20260401/candidate_b_minlib_granularity/comparison.json
results/20260401/candidate_b_minlib_granularity/comparison.csv
results/20260401/candidate_b_minlib_granularity/summary.md
results/20260401/candidate_b_minlib_granularity/bundled/atlas.json
results/20260401/candidate_b_minlib_granularity/split/atlas.json
results/20260401/candidate_b_minlib_granularity/bundled/case_<bid>/summary.json
results/20260401/candidate_b_minlib_granularity/bundled/case_<bid>/sen24.manifest.json
results/20260401/candidate_b_minlib_granularity/split/case_<sid>/summary.json
results/20260401/candidate_b_minlib_granularity/split/case_<sid>/sen24.manifest.json
scripts/validate_m3_candidate_b_evidence.py
```

The `<bid>` and `<sid>` sets are exactly the 16 block-aligned rows in Appendix C
plus the two non-block-aligned singleton split cases `case_110101` and
`case_111001`.

Fallback path:

```text
Bind the audit to an immutable release containing:
- source SHA;
- evidence tree checksum manifest;
- tag or release URL;
- DOI if available;
- validation transcript.
```

Do not include repair-liftability results in PR-M3-EVIDENCE.

## 21. Future status-update conditions

Only after PR-M3-CORE is merged should a later status PR update:

```text
README.md
RESEARCH_STATUS.md
docs/research_program_current.md
papers/README.md
```

Status update prerequisites:

1. M3 theorem core canonical on `main`.
2. Source branch SHA recorded.
3. No claim that Candidate B is Lean-formalized.
4. Candidate B marked either evidence-bound or deferred.
5. Arrow still marked future work outside doctoral completion scope.

## 22. Kill switches for implementation

Future implementation must stop if any of these occur:

1. Source SHA differs from `1c2b9e7b979ba1a4b08c1d69f5400907cf2ca689` without a
   fresh audit.
2. Any of the five Reportability files fail against current `main`.
3. Any unexpected custom axiom appears.
4. Any `sorry` or `admit` appears in PR-M3-CORE.
5. PR-M3-CORE requires changing Sen/BaseCase24/Lifting/SAT/CNF code.
6. PR-M3-CORE needs solver, CNF, LRAT, atlas, or repair enumeration execution.
7. Candidate B prose is merged without canonical evidence or release binding.
8. Candidate B is described as semantic or Lean-level social-choice validity.
9. Arrow is made a doctoral requirement or an M3 application.
10. M2.1 or repair-liftability material is pulled into M3 core.
11. Whole-branch merge becomes the integration path.
12. Source `SocialChoiceAtlas.lean` is copied wholesale.
13. Source `.gitignore` is copied without a separate ignore-policy review.
14. Status docs claim M3 is canonical before the core PR merges.

## 23. Integration readiness verdict

```text
Precheck task:
  PASS

M3 theorem-core integration:
  GO_CLEAN_EXTRACTION

Candidate B application:
  READY_WITH_CURATED_EVIDENCE

Primary theorem-core integration strategy:
  clean file extraction from source SHA 1c2b9e7b979ba1a4b08c1d69f5400907cf2ca689
  plus patch-only root imports

Whole-branch merge:
  PROHIBITED

New theorem required before core integration:
  no

New experiment required before core integration:
  no

Documentation revision required:
  yes

Evidence integration required for theorem core:
  no

Evidence integration required for Candidate B claim:
  yes

M4 blocking status after theorem-core integration:
  cleared
```

## 24. Remaining deficiencies

1. The M3 theorem core has non-fatal Lean linter warnings. They do not block
   integration but can be cleaned in PR-M3-CORE if desired.
2. The source branch root import file is stale relative to current `main`.
3. The source branch `.gitignore` is not part of theorem-core integration.
4. Several M3 documents are planning-era scaffolds and must not be integrated
   as current canonical documentation.
5. Candidate B evidence is complete off-main but still mutable until curated
   evidence or release binding is canonical.
6. No dedicated Candidate B M3 evidence validator is canonical yet.
7. Candidate B remains artifact-defined and does not become semantic or
   Lean-level social-choice validity.
8. Arrow material remains future-work scope discipline, not an M3 doctoral
   requirement.

## Appendix A. Unique commit table

| Full SHA | Date | Subject | Changed paths or path families | Category | Commit purity | Suitable for future cherry-pick | Reason |
| --- | --- | --- | --- | --- | --- | --- | --- |
| `49b5c2ba56b7310280e9a9c28b9fcca8581cda8e` | 2026-06-07T20:16:38+09:00 | paper(m2.1): scaffold transferred repair explanation manuscript | `papers/m2_1/**` | `M2_1` | pure | no | Not part of M3 theorem core |
| `54581c0c719ade024413371c137e036390c40140` | 2026-06-11T20:26:23+09:00 | fix(bib): correct author name for Reiter and update Lean 4 reference details | `.gitignore`; `docs/m3_reportability_contract.md`; `papers/m2_1/**` | `MIXED` | mixed | no | Mixes doc, ignore policy, and M2.1 bibliography |
| `058cea34f7d58c8944a6b989f2740f985b3b7c93` | 2026-06-11T20:37:25+09:00 | Strengthen M3 reportability contract | `docs/m3_reportability_contract.md` | `M3_STALE_SCAFFOLD` | pure | no | Needs revision for M3-A/B/C hierarchy |
| `778c49372df37df37fead4bb380c424f06195124` | 2026-06-11T20:41:27+09:00 | refactor(m3): update section on grouped repair invariance and clarify definitions | `docs/m3_reportability_contract.md` | `M3_STALE_SCAFFOLD` | pure | no | Needs revision before canonical docs |
| `761c8aa6013718158789bf4c71ad192ade9f8ade` | 2026-06-11T20:47:55+09:00 | feat(m3): add M3 Atomicity Theorem skeleton with definitions and lemmas | `docs/m3_atomicity_theorem_skeleton.md` | `M3_STALE_SCAFFOLD` | pure | no | Superseded by Lean theorem core |
| `0bfefc5f6f50a89c0232b3ad8309c2795c4b318d` | 2026-06-11T20:56:48+09:00 | feat(m3): add Lemma 2.5 on block-alignment closure under atomicity and update related proofs | `docs/m3_atomicity_theorem_skeleton.md` | `M3_STALE_SCAFFOLD` | pure | no | Superseded by Lean theorem core |
| `a9c6c5d142d72d830223e626aab4056263966f4a` | 2026-06-11T21:50:08+09:00 | feat(m3): add M3 Non-Atomic Group-Soundness Skeleton with motivation, core ideas, definitions, and proof structure | `docs/m3_nonatomic_group_soundness_skeleton.md` | `M3_STALE_SCAFFOLD` | pure | no | Superseded by Lean theorem core |
| `4f4e2792aff3e6eb20abb99e7e9c7930e8d99ee1` | 2026-06-11T22:02:27+09:00 | feat(m3): add candidate converse under contract deletion-monotonicity and related theorem M3-C | `docs/m3_nonatomic_group_soundness_skeleton.md` | `M3_STALE_SCAFFOLD` | pure | no | Calls M3-C candidate; Lean now proves it |
| `41470afe83361dd208546c5a7d26ffefe2498ccc` | 2026-06-12T08:04:18+09:00 | feat(m3): enhance M3-B with focus on UNSAT repair setting and clarify implications of Psi-deletion-monotonicity | `docs/m3_nonatomic_group_soundness_skeleton.md` | `M3_STALE_SCAFFOLD` | pure | no | Historical scaffold |
| `916d82a7ab173ecb1b526ac78794e48833762002` | 2026-06-12T08:18:12+09:00 | feat(m3): add M3 Candidate B GroupSoundness Audit Plan document | `docs/m3_candidate_b_group_soundness_audit_plan.md` | `M3_CANDIDATE_B_AUDIT` | pure | yes, only with evidence | Path-dependent audit plan |
| `133ba19d96921dc6d51b1e5127573c8bbee27da9` | 2026-06-12T08:28:02+09:00 | feat(m3): add M3 Candidate B GroupSoundness Audit Result document | `docs/m3_candidate_b_group_soundness_audit_result.md` | `M3_CANDIDATE_B_AUDIT` | pure | yes, only with evidence | Requires canonical evidence binding |
| `5d1e29ff288e00ed6a0f2cf4b590511dfbf58256` | 2026-06-12T08:33:48+09:00 | data: publish audit-relevant results (json/csv/md only) | `.gitignore`; `results/20260401/candidate_b_minlib_granularity/**`; `results/20260401/repair_liftability/**` | `MIXED` | mixed | no | Mixes Candidate B, unrelated repair-liftability, and ignore policy |
| `9690aa3d5b7f4754b8599cdc95a592379e08eeeb` | 2026-06-12T08:39:19+09:00 | refactor(m3): rename section to 'Audit Verdict Checklist' for clarity | `docs/m3_candidate_b_group_soundness_audit_result.md` | `M3_CANDIDATE_B_AUDIT` | pure | yes, only with evidence | Documentation-only but path-dependent |
| `ab6df5d761e040b7940cea2cf32306a4157bdc21` | 2026-06-12T08:54:00+09:00 | feat(m3): add comprehensive transition document from M1.5 to M3 detailing reportability and contract implications | `docs/m1_5_to_m3_transition.md` | `M3_CURRENT_DOC` | pure | yes, after revision | Mostly current but should follow core integration |
| `79d59fa6ea5194d4662d238f00e1981fe0dc1d1f` | 2026-06-12T08:59:28+09:00 | feat(m3): enhance M3-B documentation with GroupSoundness and audit implications | `docs/m1_5_to_m3_transition.md` | `M3_CURRENT_DOC` | pure | yes, after revision | Mostly current but should follow core integration |
| `00e38976c707158dad30375b5739bb0b791999a6` | 2026-06-12T09:18:39+09:00 | feat(m2b): add M2b Arrow Transfer Prerequisites document outlining framework and obligations | `docs/m2b_arrow_transfer_prerequisites.md` | `ARROW_EXCLUDED` | pure | no | Outside doctoral M3 scope |
| `54d1bfe1125d97ca183689491040024bbc0a9cc7` | 2026-06-12T21:07:49+09:00 | feat(m3): create M3 Paper Section Allocation document outlining manuscript structure and planning | `docs/m3_paper_section_allocation.md` | `M3_STALE_SCAFFOLD` | pure | no | Planning doc with stale pending statuses |
| `2549d6615a8bfbf389e465f9f81ffb1065d066cf` | 2026-06-12T22:53:39+09:00 | Add M3 reportability definitions and examples | `SocialChoiceAtlas.lean`; `SocialChoiceAtlas/Reportability/**` | `MIXED` | mixed | no | Contains good theorem core plus stale root glue |
| `6736cb00e6621e2dfeea91d6dca9e30888185d86` | 2026-06-13T00:04:22+09:00 | feat(m3): refine M1.5 to M3 transition document with enhanced clarity on reportability and abstraction-contract thesis | `docs/m1_5_to_m3_transition.md` | `M3_CURRENT_DOC` | pure | yes, after revision | Mostly current |
| `1c2b9e7b979ba1a4b08c1d69f5400907cf2ca689` | 2026-06-13T00:10:26+09:00 | feat: update focus description in SocialChoiceAtlas and clarify audit process in M1.5 to M3 transition documentation | `SocialChoiceAtlas.lean`; `docs/m1_5_to_m3_transition.md` | `MIXED` | mixed | no | Mixes stale root glue with doc revision |

## Appendix B. File/blob/hash table

Key source blobs at `origin/codex/m3-lean-reportability`:

| Path | Blob SHA | Proposed disposition |
| --- | --- | --- |
| `SocialChoiceAtlas/Reportability/Atomic.lean` | `ce4c371869f8884093cd69c594e7b32fe70b7029` | PR-M3-CORE |
| `SocialChoiceAtlas/Reportability/Defs.lean` | `03053943a8f2429c79340734a23b0b0609058e9b` | PR-M3-CORE |
| `SocialChoiceAtlas/Reportability/Examples.lean` | `14ce4b823795056f9cb91814acf83fb1b4fedcbe` | PR-M3-CORE |
| `SocialChoiceAtlas/Reportability/GroupSound.lean` | `2ef41b003d63088bc762a493c6ed1590d2996293` | PR-M3-CORE |
| `SocialChoiceAtlas/Reportability/Monotone.lean` | `37958d0c63c835365a8dda94ec615f7e5ff719f4` | PR-M3-CORE |
| `docs/m1_5_to_m3_transition.md` | `7e9842f83f49408d8a70a28bc7e04f3429b78cbf` | revise after core |
| `docs/m3_candidate_b_group_soundness_audit_result.md` | `b242891a5f4012dc253d0db1fe322b3cd342394b` | integrate only with evidence |
| `results/20260401/candidate_b_minlib_granularity/comparison.json` | `84b0036a80f019fb3ee4efe754be6c19382342b9` | curated evidence |
| `results/20260401/candidate_b_minlib_granularity/bundled/atlas.json` | `8ecfe398f8fad1a33c8ee6454fd10ce313afd43d` | curated evidence |
| `results/20260401/candidate_b_minlib_granularity/split/atlas.json` | `962e995305184839683fed1c0404f6b87be11bf6` | curated evidence |

Candidate B tree integrity:

| Metric | Value |
| --- | --- |
| Files | 197 |
| Bytes | 327877 |
| Zero-byte files | 0 |
| Malformed JSON files | 0 |
| LFS pointers | 0 |
| Symlinks | 0 |
| Summary/manifest CNF hash mismatches | 0 |

## Appendix C. Evidence-path table

The audited contract fixes `no_cycle3 = off`. Bundled bit order is:

```text
[asymm, un, minlib, no_cycle3, no_cycle4]
```

Split bit order is:

```text
[asymm, un, decisive_voter0, decisive_voter1, no_cycle3, no_cycle4]
```

Sixteen block-aligned residual rows:

| Retained `T ⊆ I` | Bundled case | Split block case | Bundled status | Split status | Match |
| --- | --- | --- | --- | --- | --- |
| `∅` | `case_00000` | `case_000000` | SAT | SAT | PASS |
| `{asymm}` | `case_10000` | `case_100000` | SAT | SAT | PASS |
| `{un}` | `case_01000` | `case_010000` | SAT | SAT | PASS |
| `{asymm, un}` | `case_11000` | `case_110000` | SAT | SAT | PASS |
| `{minlib}` | `case_00100` | `case_001100` | SAT | SAT | PASS |
| `{asymm, minlib}` | `case_10100` | `case_101100` | SAT | SAT | PASS |
| `{un, minlib}` | `case_01100` | `case_011100` | SAT | SAT | PASS |
| `{asymm, un, minlib}` | `case_11100` | `case_111100` | SAT | SAT | PASS |
| `{no_cycle4}` | `case_00001` | `case_000001` | SAT | SAT | PASS |
| `{asymm, no_cycle4}` | `case_10001` | `case_100001` | SAT | SAT | PASS |
| `{un, no_cycle4}` | `case_01001` | `case_010001` | SAT | SAT | PASS |
| `{asymm, un, no_cycle4}` | `case_11001` | `case_110001` | SAT | SAT | PASS |
| `{minlib, no_cycle4}` | `case_00101` | `case_001101` | SAT | SAT | PASS |
| `{asymm, minlib, no_cycle4}` | `case_10101` | `case_101101` | SAT | SAT | PASS |
| `{un, minlib, no_cycle4}` | `case_01101` | `case_011101` | SAT | SAT | PASS |
| `{asymm, un, minlib, no_cycle4}` | `case_11101` | `case_111101` | UNSAT | UNSAT | PASS |

Split singleton deletion rows from the fully active split case `case_111101`:

| Deleted split lever | Retained split case | Status | Grouped report |
| --- | --- | --- | --- |
| `asymm` | `case_011101` | SAT | `{asymm}` |
| `un` | `case_101101` | SAT | `{un}` |
| `decisive_voter0` | `case_110101` | SAT | `{minlib}` |
| `decisive_voter1` | `case_111001` | SAT | `{minlib}` |
| `no_cycle4` | `case_111100` | SAT | `{no_cycle4}` |

Grouped family reconstructed from the singleton repairs:

```text
{{asymm}, {un}, {minlib}, {no_cycle4}}
```
