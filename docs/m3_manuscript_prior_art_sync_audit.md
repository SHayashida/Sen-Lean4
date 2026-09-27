# M3 manuscript prior-art synchronization audit

Status: editorial claim-synchronization audit for the integrated M1.5+M3
manuscript

Scope: `papers/cpp2027_m1_5_m3/main.tex` and its bibliography

This document is not a theorem, a literature survey, or evidence for a new
scientific result. It records why the manuscript was minimally changed to
match `docs/m3_prior_art_claim_matrix.md` and the current Lean source.

## Authority and method

The audit used the required authority order:

1. `SocialChoiceAtlas/Reportability/*.lean` for theorem statements;
2. `docs/m3_prior_art_claim_matrix.md` for prior-art positioning;
3. the mechanically frozen `m3/candidate_b/` package for Candidate B claims;
4. manuscript prose.

The pre-edit manuscript was searched for `novel`, `first`, `to our knowledge`,
`formalized`, `abstraction`, `report`, `faithful`, `canonical`, `exact`, `if
and only if`, `iff`, `group`, `minimal`, `certificate`, `diagnosis`, `MUS`, and
`MCS`. The search produced 165 line matches. Routine uses in definitions,
proof sketches, and artifact descriptions were checked against the governing
Lean declarations or evidence boundary. The table below records every
substantive claim that required an explicit support classification; unchanged
routine terminology is not reproduced line by line.

## Claim-by-claim audit

| ID | Location | Old wording or claim | Classification | New wording or disposition | Reason and authority |
|---|---|---|---|---|---|
| A01 | Abstract, former lines 44--49 | “grouped repair reports coincide with contract-level repairs precisely when the realization is group sound, for deletion-monotone reference contracts” | `THEOREM_WORDING_MISMATCH` | Adds disjointness and residual faithfulness; identifies the target predicate as separately specified but explicitly bridged. | `groupSoundness_iff`; matrix P1 and P6. |
| A02 | Introduction contribution 1 | The no-go witness establishes non-canonicity of the raw family under the studied representation change. | `SUPPORTED_AS_WRITTEN` | Core witness claim retained; one sentence now says it is not a generic novelty claim for post-hoc mapping or changes of minimal families. | Artifact claims C1--C5; matrix P2 and P3. |
| A03 | Introduction, former contribution 2 | One item combined the reporting interface, sufficiency, exactness, and two-realization result. | `SUPPORTED_AFTER_NARROWING` | Split into a separately specified reporting-semantics contribution and an exactness/audit-boundary contribution, with all hypotheses stated. | `m3b_grouped_correctness`, `m3b_two_realization`, `m3c_converse`, and `groupSoundness_iff`. |
| A04 | Introduction and characterization | Audit reduction from raw minimal repairs was absent from the paper-facing contribution summary. | `SUPPORTED_AFTER_NARROWING` | Adds a bounded “audit-cost collapse” lemma and states that no deletion monotonicity of `SatPhi` is assumed. | `audit_cost_collapse`; matrix P6. |
| A05 | Introduction claim-boundary paragraph | “all statements” in the contract and characterization sections were called Lean theorems. | `SUPPORTED_AFTER_NARROWING` | Limits kernel-checking to the definitions and numbered theorem/corollary/lemma/example claims, and excludes the labeled future question. | Current Lean declarations; matrix current-versus-proposed boundary. |
| A06 | Contract definition | `SatPsi` and `SatPhi` were separately introduced, but their non-definitional relationship and bridge qualification were implicit. | `SUPPORTED_AFTER_NARROWING` | States that `SatPsi` is not definitionally constructed from `SatPhi` or the reporting map and is not arbitrary because `ResidualFaithfulness` is the bridge. | `Defs.lean`: independent predicate arguments and `ResidualFaithfulness`; matrix P1. |
| A07 | Atomicity discussion, former lines 373--376 | Atomic grouping was called a “rarely stated folklore assumption” under which reports are silently canonical. | `OVERBROAD_PRIOR_ART_CLAIM` | Replaced with the formal hierarchy: atomicity is a strong syntactic sufficient regime and is not necessary. | `m3a_grouped_correctness`, `atomicity_implies_groupSoundness`, and `Examples.NonAtomic`; matrix P5. |
| A08 | Boundary-example synthesis, former lines 477--480 | “group soundness sits strictly between atomicity and mere correctness of grouped reports” | `THEOREM_WORDING_MISMATCH` | Separates the two demonstrated facts: atomicity is not necessary; without target-side monotonicity grouped correctness need not imply group soundness. | `Examples.NonAtomic` and `Examples.NonMonotone`. |
| A09 | Theorem `thm:suff` | Disjoint blocks, residual faithfulness, and group soundness imply grouped/contract coincidence. | `SUPPORTED_AS_WRITTEN` | Unchanged. | `m3b_grouped_correctness`. No monotonicity is added. |
| A10 | Theorems `thm:conv` and `thm:iff` | The converse uses reference deletion monotonicity without residual faithfulness; the combined iff additionally uses disjointness and residual faithfulness. | `SUPPORTED_AS_WRITTEN` | Unchanged apart from surrounding explanatory precision. | `m3c_converse` and `groupSoundness_iff`. |
| A11 | Concrete-instance claim boundary | Concrete group soundness is artifact-audited and not Lean-formalized. | `SUPPORTED_AS_WRITTEN` | Retained; the earlier partial-block paragraph now explicitly points to this artifact-level audit. | `m3/candidate_b/CLAIM_BOUNDARY.md` and `GroupSound.lean` docstring. |
| A12 | Related Work, formalized social choice, former lines 583--584 | “the meta-theory of the reports derived from such theorems, which to our knowledge has not been formalized” | `OVERBROAD_PRIOR_ART_CLAIM` | Replaced with a positive scope statement: contract-relative justification of reports derived from verified low-level repairs. | The matrix is not an exhaustive absence proof; P1/P4 contain `No△` classifications. |
| A13 | Related Work, diagnosis/MUS-MCS | Existing paragraph could imply novelty for group-level granularity and regrouping effects. | `SUPPORTED_AFTER_NARROWING` | Explicitly concedes minimal-set machinery and grouping as established substrate. | Matrix P2/P3/P5 and `ESTABLISHED_SUBSTRATE_NOT_NOVELTY`. |
| A14 | Related Work, hierarchical/structural diagnosis | No distinct discussion of hierarchical or structural diagnosis abstraction. | `OVERBROAD_PRIOR_ART_CLAIM` | Adds a concise paragraph conceding multilevel diagnosis, coarse vocabularies, and model abstraction to prior work. | Matrix rows Mozetić 1991 and Chittaro & Ranon 2004. |
| A15 | Related Work, post-hoc abstraction | Grastien et al. 2023 and its projection/minimization result were absent. | `OVERBROAD_PRIOR_ART_CLAIM` | Adds the required strong-prior-art concession for projection, re-minimization, and changes to minimal families. | Matrix P2=`Yes` and P3=`Yes` for Grastien et al. 2023. |
| A16 | Related Work, abstraction, former lines 602--607 | “our contribution is an exact (iff) condition, mechanized, for when abstraction-level repair reporting is faithful” | `SUPPORTED_AFTER_NARROWING` | Limits the claim to reinterpretation under separately specified target semantics and to the current `ResidualFaithfulness`/`GroupSoundness`/target-monotonicity interface. | `groupSoundness_iff`; matrix P1, P4, and P6. |
| A17 | Related Work, certificates | Certificates/checkers were described as complementary but not expressly conceded as non-novel. | `SUPPORTED_AFTER_NARROWING` | Explicitly says certificates and checkers in general are not the novelty claim. | Matrix P8. |
| A18 | Conclusion, former lines 617--621 | `groupSoundness_iff` was summarized as “exactly what canonical reporting requires,” and realization independence was unqualified. | `THEOREM_WORDING_MISMATCH` | States all iff hypotheses and limits realization independence to the group-sound, residually faithful realizations covered by the corollary. | `groupSoundness_iff` and `m3b_two_realization`. |
| A19 | Whole manuscript | No use of `FrontierSoundness`, `CRLift`, `ReverseLiftability`, or `GC <-> FS ∧ CRLift` was found. | `SUPPORTED_AS_WRITTEN` | None added. | Matrix P4: `PROPOSED_THEOREM`, not currently implemented. |
| A20 | Whole manuscript | No claim that the weakest pre-group/post-hoc equivalence condition is known was found. | `SUPPORTED_AS_WRITTEN` | Adds one explicitly future-facing sentence asking for a weaker-than-atomic characterization. | Matrix P5: proposed theorem, not currently proved. |
| A21 | Whole manuscript | No Autio & Reiter universal absence claim was found. | `SUPPORTED_AS_WRITTEN` | No Autio & Reiter absence claim added. | Matrix uses `not reported†` and `unknown†`; original source remains unavailable. |
| A22 | M1.5 interpretation | The negative witness motivates the contract theory by showing raw-report non-canonicity under the studied change. | `SUPPORTED_AS_WRITTEN` | Preserved as motivation and separated from the constructive M3 theorem contributions. | M1.5 C1--C5 evidence boundary and matrix P2/P3 concessions. |

## Contribution wording before and after

### Before

The contribution list had three items: a no-go theorem; a single broad
“characterization” item combining the full M3 chain; and mechanization plus
artifact evidence. It did not expressly disclaim novelty for projection or
minimal-family change, and it did not expose `audit_cost_collapse`.

### After

The list has four bounded roles:

1. the M1.5 negative witness as motivation, without a generic abstraction or
   minimization novelty claim;
2. the current M3 separately specified target semantics, explicit
   `ResidualFaithfulness` bridge, and M3-B sufficiency;
3. M3-C exactness and audit reduction under target-side deletion monotonicity,
   explicitly without `SatPhi` monotonicity; and
4. Lean mechanization separated from concrete artifact evidence.

No proposed theorem is promoted into the contribution list.

## Related Work synchronization

The revised section now distinguishes:

1. model-based diagnosis and MUS/MCS;
2. hierarchical and structural diagnosis abstraction;
3. post-hoc diagnosis projection and re-minimization, with Grastien et al.
   2023 treated as strong prior art;
4. adjacent abstraction theory and its established preservation distinctions;
5. certificates and certified checkers.

It then states the narrower current question: reinterpretation of verified
low-level repairs under a separately specified target reporting semantics,
characterized through `ResidualFaithfulness`, `GroupSoundness`, and target-side
deletion monotonicity. The manuscript does not reproduce the 7 × 8 matrix.

## Candidate B freeze impact

The authoritative branch contains no paper-level Candidate B claim-map file
that hashes `papers/cpp2027_m1_5_m3/main.tex` or `refs.bib`. The frozen
`m3/candidate_b/` package does not include either manuscript file in its
manifest or theorem binding. The scientific Candidate B claims were not
changed.

```text
AFFECTED_CANDIDATE_B_CLAIM_IDS = none
CANDIDATE_B_CLAIM_FREEZE_REQUIRES_REFRESH = NO
```

## Validation record

The manuscript built to a seven-page PDF with no unresolved citation or
cross-reference. Existing non-fatal BibTeX metadata and layout warnings remain;
they are outside this claim-synchronization task. The M3 smoke gate and axiom
audit passed with the repository's existing linter warnings. The Candidate B
package rebuilt its 99-file curated whitelist, verified its manifest, rejected
all 15 mandatory fault injections, passed its validator and unit test, replayed
the M3 smoke gate, and produced no package diff.

```text
PRIOR_ART_OVERCLAIM = 0
LEAN_THEOREM_MISMATCH = 0
SATPHI_MONOTONICITY_MISCLAIM = 0
CURRENT_FUTURE_CONFLATION = 0
GRASTIEN_UNDERCITATION = 0
AUTIO_REITER_OVERCLAIM = 0
NEW_THEOREM_CLAIMS = 0
NEW_EXPERIMENTS = 0
MANUSCRIPT_BUILD = PASS
M3_LEAN_SMOKE = PASS
CANDIDATE_B_VALIDATION = PASS
CANDIDATE_B_CLAIM_FREEZE_REQUIRES_REFRESH = NO
M3_MANUSCRIPT_PRIOR_ART_SYNC = PASS
```
