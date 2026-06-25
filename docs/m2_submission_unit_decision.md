# M2 Submission-Unit Decision

## 1. Decision identity

- Repository: `SHayashida/Sen-Lean4`
- Audit branch: `codex/m2-one-time-reviewer-audit`
- Decision date: 2026-06-26 Asia/Tokyo
- Baseline `origin/main`: `90feec20154fa4610634b0d8ec059f8e8c018169`
- M2 archived tag: `papers-m2-v2-obstruction-bridge`
- M2 archived commit: `d7e5fd1ac94ab18330951b5d9741585dddc5b43a`

This decision evaluates submission configuration only. It does not merge papers
or alter the M2 manuscript, Lean code, bibliography, tag, release, or DOI.

## 2. Inputs from the novelty audit

- Overall novelty verdict: `MODERATE`.
- Mathematical novelty: low to none for the Sen theorem itself.
- Mechanization novelty: moderate for a Lean-checked Sen obstruction
  factorization.
- Interface/factorization novelty: moderate to high for the public
  `SenRightsWitness`, classified witness, and outcome-obstruction ladder.
- Methodological novelty: moderate for the Proof-layer vs Witness/Audit-layer
  Transfer Contract framing, if presented as claim discipline rather than a new
  artifact-transport theorem.
- Closest prior work: Sen 1970 for theorem content; Nipkow 2009 and AFP for
  mechanized social-choice precedent; Tang/Lin, Geist/Endriss, Brandt/Geist
  for automated finite social-choice evidence; Grandi/Endriss for lifting
  methodology; DRAT/LRAT work for proof-certificate boundaries.

## 3. Inputs from the adversarial review

- Adversarial verdict: `PASS WITH MAJOR REVISION`.
- Fatal objections: none.
- Major blockers before submission: novelty framing, `basis`/`canonical`
  terminology, theorem-vs-policy labeling, stale four-contract nomenclature,
  related-work incompleteness, and self-containment.
- New theorem required for a minimal viable submission: no.
- New experiment required for a minimal viable submission: no.
- M2 remains valid as the dissertation semantic bridge.

## 4. Candidate publication units U1-U5

| Unit | Assessment |
|---|---|
| U1. M2 as standalone Social Choice and Welfare article | Plausible after major revision. Subject fit is strong, but novelty must be framed as verified factorization and artifact-boundary discipline, not new Sen mathematics. |
| U2. M2 as standalone Journal of Automated Reasoning article | Plausible but higher risk. The formalization may be too small unless the proof-engineering/interface lesson is sharpened and the unformalized scope wall is clearly labeled. |
| U3. M2 as computational-social-choice / AI venue paper | Weak as a standalone AI paper. There is no new SAT method, experiment, or AI technique. JAIR-style venues would require a stronger AI-significance story. |
| U4. M2 integrated with M1 as an Evidence + Transfer article | Scientifically coherent but expensive. It may strengthen significance, but it would merge archival stories and delay M4. Not required before M4. |
| U5. M2 retained as dissertation chapter / technical report only | Safe fallback if revision appetite is low or if external novelty review rejects the standalone framing. The chapter value is independent of paper acceptance. |

## 5. Current venue-policy verification

Access date: 2026-06-26.

Social Choice and Welfare:

- Official aims page states that the journal covers welfare economics,
  collective choice, strategic interaction, preference aggregation, rights,
  voting, computational social choice, judgment aggregation, and choice/order
  theory with applications to these topics.
- Official author guidelines accept LaTeX manuscripts, require a concise
  informative title, a 150-250 word abstract, editable source files, and
  standard publication/originality assurances.
- Manuscript type observed on the current journal page: "Original Paper".
- Fit implication: topic fit is strong; contribution-strength risk is the main
  issue.

Journal of Automated Reasoning:

- Official aims page covers theory, implementation, and applications of logical
  reasoning by computer, including formal proof assistants, automatic theorem
  provers, proof systems, formalized mathematics, and case studies that teach
  lessons about tool use.
- Official guidelines specify single-blind review, editable source files,
  150-250 word abstract, 4-6 keywords, and normal originality assurances.
- Manuscript type observed on current journal page: "Original Paper".
- Fit implication: formal-methods fit is real, but M2 must explain reusable
  proof-engineering lessons beyond a small domain case study.

JAIR / computational-social-choice or AI venue:

- JAIR's official charter covers all AI areas, including automated reasoning,
  constraint processing and search, and multi-agent systems.
- JAIR requires originality, significance, clear claims, empirical evidence or
  theoretical analysis, and an explanation of how the work matters to the AI
  community. Its submission checklist warns against narrow or merely applied
  uses of known AI techniques.
- Fit implication: M2 is not currently a strong JAIR submission because it has
  no new AI method or experiment and is better aligned with social choice or
  formalized mathematics.

## 6. Recent adjacent-paper comparison

Social Choice and Welfare recent adjacent articles inspected from the current
official journal page:

| Recent article | Relevance to M2 |
|---|---|
| "Experimental results on the roommate problem" | Shows broad social-choice/matching fit, but empirical rather than formal. |
| "On the ordinal Bayesian incentive compatibility of vote share and veto share rules" | Voting-theory mechanism result; closer to SCW mathematical readership. |
| "Do grades have absolute meaning? An experiment on majority judgment" | Social-choice voting topic; empirical. |
| "Formation of teams in contests: tradeoffs between inter- and intra-team inequalities" | Welfare/strategic-interaction topic; not formal methods. |
| "Arrovian independence and the aggregation of choice functions" | Closest topical comparison: axiomatic aggregation and Arrovian conditions. |

Journal of Automated Reasoning recent adjacent articles inspected from the
current official journal page:

| Recent article | Relevance to M2 |
|---|---|
| "Typed Compositional Quantum Computation with Lenses" | Formalization/theory article; shows high formal-methods depth expectation. |
| "YALLA: Yet Another Deep Embedding of Linear Logic in Rocq" | Proof-assistant embedding; suggests reusable tool/formalization lessons matter. |
| "Verified Tableaux: from Modal Logics to Modal Fixpoint Logics" | Verified reasoning framework; stronger method contribution than M2 currently has. |
| "The Rewster: Type Preserving Rewrite Rules for the Rocq Prover" | Tool/prover contribution; not merely application-domain formalization. |
| "Targeting Completeness: Automated Complexity Analysis of Integer Programs" | Automated reasoning/application method; broader tool significance. |

JAIR recent adjacent articles inspected from the current issue:

| Recent article | Relevance to M2 |
|---|---|
| "Causal Explanations for Image Classifiers" | AI explanation/significance; not close. |
| "Explaining Multivariate Decision Trees" | Logic/tractability/explanation; method-oriented. |
| "Machine Learning-Guided Interactive Constraint Acquisition" | Constraint/learning method; closer to AI search but not social choice. |
| "R-Mod: Minimal Structural Revision of S5 Epistemic Models" | Logic/model revision; shows technical AI-theory fit expectations. |
| "Differential Parity" | Fairness criterion; societal decision context but not formal social-choice proof. |

## 7. Venue-fit scoring matrix

Scores are 0-5. They are not acceptance probabilities.

| Unit / venue | Subject fit | Novelty fit | Technical depth | Significance | Self-containment | Artifact strength | Expository readiness | Revision cost |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| U1. Standalone SCW | 5 | 3 | 3 | 3 | 3 | 3 | 2 | 3 |
| U2. Standalone JAR | 3 | 3 | 3 | 2 | 3 | 4 | 2 | 2 |
| U3. AI/JAIR-style venue | 2 | 2 | 2 | 2 | 3 | 3 | 2 | 2 |
| U4. Integrated M1+M2 article | 4 | 4 | 4 | 4 | 4 | 5 | 1 | 1 |
| U5. Thesis/technical report only | 5 | 4 | 4 | 4 | 5 | 5 | 4 | 5 |

Risk summary:

| Unit / venue | Desk-reject risk | Reviewer rejection risk | Confidence |
|---|---|---|---|
| U1. Standalone SCW | medium | medium-high | medium |
| U2. Standalone JAR | medium-high | high | medium |
| U3. AI/JAIR-style venue | high | high | medium |
| U4. Integrated M1+M2 article | medium | medium | low |
| U5. Thesis/technical report only | low | low | high |

## 8. Standalone contribution test

M2 passes the standalone contribution test conditionally.

It should proceed as a standalone submission only if the central contribution is
stated as:

> A kernel-checked public factorization of Sen's known liberal-paradox
> contradiction through reusable obstruction objects, paired with an explicit
> artifact-boundary statement separating semantic theorem transfer from finite
> CNF/LRAT witness transfer.

It should not proceed if the manuscript continues to imply:

- a new social-choice impossibility theorem;
- a minimal, unique, or irredundant obstruction basis;
- a theorem that lifts the Sen24 CNF atlas;
- a completed multi-theorem-family transfer theory.

## 9. Integration-with-M1 test

U4 is intellectually coherent because M1 supplies the finite Evidence Contract
and M2 supplies the semantic transfer boundary. Integration could improve
significance by presenting a larger end-to-end audit story.

However, integration is not required before M4. It would require substantial
paper restructuring, comparison of two release identities, and a fresh
submission-unit decision. The current audit therefore does not recommend U4 as
the next action.

## 10. Required revision package

Minimum viable revision package before submission:

| Item | Classification |
|---|---|
| Replace or qualify prominent `basis` wording. | required |
| Remove `canonical` except where explicitly defined as non-unique/non-minimal. | required |
| Reframe theorem novelty as known mathematics plus new mechanized factorization. | required |
| Expand Sen-specific rights literature and mechanized-social-choice related work. | required |
| Rewrite the finite-atlas relationship as discovery/audit context, not theorem premise. | required |
| Separate theorem claims from audit-policy and program-framing claims. | required |
| Align program nomenclature with M1/M1.5/M2/M3/M4. | required |
| Reduce forward dependence on unpublished companion papers. | required |
| Add venue-facing self-contained motivation. | required |
| Preserve release/DOI/source-snapshot distinctions. | required |

Strong revision package:

| Item | Classification |
|---|---|
| Lean formalization of the 5-cycle scope-wall witness. | recommended |
| Compact formal correspondence theorem between raw overlap branches and paper-facing O2/O3/O4 objects. | recommended |
| Reusable abstract transfer-contract schema beyond the single Sen case. | optional |
| Additional independent mechanized case study. | out of scope for M2 |
| New solver or atlas experiments. | out of scope |

## 11. No-go conditions

Do not submit M2 if any of the following remain:

- `basis` or `canonical` is readable as minimality, uniqueness, irredundancy, or
  normal form.
- The abstract or introduction suggests that the Sen24 CNF/LRAT/atlas lifts.
- The manuscript claims a new Sen theorem rather than a verified
  factorization/interface contribution.
- The scope wall is described as a Lean theorem.
- Related work omits the main Sen-rights and mechanized-social-choice sources.
- Four-contract nomenclature conflicts with the locked dissertation spine.
- The paper depends on unpublished M1.5, M2.1, M3, or M4 claims for its core
  contribution.

## 12. Primary venue

Primary venue: Social Choice and Welfare.

Rationale: The subject matter is directly within the journal's official scope:
collective choice, preference aggregation, rights, voting, computational social
choice, and choice/order theory. The main risk is not topic fit but contribution
framing. A revised manuscript must speak first to social-choice readers:
Sen's theorem is known; M2 contributes a machine-checked factorization and a
precise artifact-boundary lesson for finite evidence.

Desk-reject risk after required revisions: medium.

Reviewer-rejection risk after required revisions: medium-high.

## 13. Fallback venue

Fallback venue: Journal of Automated Reasoning, only after strengthening the
formal-methods story.

Rationale: JAR officially covers proof assistants, formalized mathematics, and
case studies that teach lessons about tool use. M2 has a real Lean artifact,
but the current paper is small compared with recent JAR proof-engineering and
tool papers, and the scope wall is not formalized. JAR is therefore a fallback
only if the revision emphasizes reusable Lean interfaces, public obstruction
objects, and proof/artifact trust boundaries more strongly than social-choice
novelty.

JAIR or a broad AI venue is not recommended as the primary fallback. M2 does
not currently introduce a new AI method, experiment, or broadly reusable search
technique.

## 14. Final decision

Decision:
  `CONDITIONAL GO`

Primary submission unit:
  Standalone M2 article after required major revisions.

Primary venue:
  Social Choice and Welfare.

Fallback venue:
  Journal of Automated Reasoning, only with stronger formal-methods framing.

Central defensible contribution:
  A kernel-checked public factorization of Sen's known liberal-paradox
  contradiction through reusable obstruction objects, paired with an explicit
  boundary between semantic Proof-layer transfer and finite CNF/LRAT
  Witness/Audit-layer transfer.

Claims to remove or weaken:
  New social-choice mathematics; minimal/unique/irredundant basis; canonical
  normal form; atlas-to-general CNF lift; Transfer Contract as a standalone
  artifact-transport theorem; multi-theorem-family bridge completion.

Required revisions before submission:
  Complete the minimum viable revision package in Section 10.

New theorem or experiment required:
  no

M2 doctoral-chapter status:
  retained

M4 blocking status:
  cleared

## 15. Consequences for the dissertation program

The audit clears M2 for dissertation use as the semantic bridge chapter. The
standalone paper is not cleared for immediate submission, but the blockers are
framing, related work, and self-containment rather than theorem correctness.

M4 may proceed after the separately planned M3 canonical integration step. The
publication decision does not broaden the doctoral scope, does not add Arrow,
does not claim family-level CNF/LRAT/atlas/repair transfer, and does not treat
M3 or M4 as complete on `main`.
