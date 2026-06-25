# M2 Adversarial Manuscript Review

## 1. Review identity and baseline

- Repository: `SHayashida/Sen-Lean4`
- Audit branch: `codex/m2-one-time-reviewer-audit`
- Review date: 2026-06-26 Asia/Tokyo
- Baseline `origin/main`: `90feec20154fa4610634b0d8ec059f8e8c018169`
- M2 archived tag: `papers-m2-v2-obstruction-bridge`
- M2 archived commit: `d7e5fd1ac94ab18330951b5d9741585dddc5b43a`

This review does not edit the manuscript. It evaluates the current M2 paper as
a skeptical pre-submission reviewer audit.

## 2. Executive editorial assessment

M2 is correct in its central repository-bound claims, but the current
manuscript is not submission-ready. The core social-choice theorem is known
mathematics. The defensible contribution is a Lean-checked public
factorization of Sen's argument, plus explicit separation between semantic
Proof-layer transfer and CNF Witness/Audit-layer non-transfer.

No fatal correctness objection was found. The submission risk is nevertheless
high without major revision because several phrases invite over-reading:
`basis`, `canonical`, `Transfer Contract`, `arbitrary voter type`, and the
four-contract program language. These can be repaired by exposition and
literature work; no new theorem or experiment is required for a minimal viable
submission.

## 3. Reviewer personas

| Persona | Primary concern |
|---|---|
| Social Choice and Welfare theorist | Whether the theorem is new social-choice mathematics and whether Sen/right literature is represented fairly. |
| Formal-methods / proof-assistant reviewer | Whether the Lean contribution is technically meaningful, reusable, and separated from informal audit claims. |
| Computational-social-choice reviewer | Whether SAT/CNF/atlas language is accurate and not sold as a new computational result. |
| Journal editor | Whether the manuscript is self-contained, novel enough, and aligned with venue expectations. |

## 4. Fatal-objection screen

| Question | Answer |
|---|---|
| Is any central claim false? | No. The inspected Lean declarations and claim-boundary docs support C1-C9 when read narrowly. |
| Is any central claim already established in essentially the same form? | The Sen impossibility theorem is established. The exact Lean public-obstruction factorization was not found in inspected prior work. |
| Does the paper lack a standalone contribution? | No, but the standalone contribution is moderate and formal/methodological, not a new theorem of social choice. |
| Does the paper misdescribe its relation to the finite atlas? | Partly. It mostly states the boundary correctly, but title and introduction can still be read as an atlas-to-general bridge unless tightened. |
| Does the scope wall rely on an unsupported assertion? | Partly. The 5-cycle witness is elementary and documented, but it is not formalized in Lean. This is a major exposition issue, not fatal. |
| Is there a venue-independent reason not to submit? | No, provided required revisions are completed first. |

## 5. Major objections

| Reviewer objection | Severity | Correct? | Affected passage | Evidence | Current defense | Required repair | New theorem/experiment? | Blocks submission? |
|---|---|---|---|---|---|---|---|---|
| O2/O3/O4 may be standard Sen proof case analysis with new names. | major | partly | `papers/m2/sections/00_abstract.tex`; `03b_contributions.tex` | Sen 1970; Gibbard 1974; rights literature | inadequate | Recast as verified factorization/interface, not new mathematical classification. | no | yes |
| "Basis" and "canonical support family" may imply minimality, uniqueness, or normal form. | major | yes | title; abstract; intro; contributions | `papers/m2/CLAIM_BOUNDARY.md` forbids minimal/unique/irredundant reading | partly adequate | Prefer "obstruction factorization" or "complete O2/O3/O4 semantic obstruction family"; remove or qualify `canonical`. | no | yes |
| Transfer Contract sounds like a theorem when it is partly audit policy. | major | yes | abstract; intro; related work; conclusion | Lean files prove semantic bridge only; scope wall is text-first | inadequate | Split theorem, proposition, audit policy, and framing explicitly. | no | yes |
| Current four-contract language is stale relative to the locked M1-M4 spine. | major | yes | introduction table and conclusion | `docs/doctoral_scope_lock.md`; `docs/research_program_current.md` | absent | Replace Evidence/Explanation/Transfer/Normative framing with M1/M1.5/M2/M3/M4 terminology or state it as historical program language. | no | yes |
| Related work is too sparse for Sen-specific rights literature and mechanized social-choice prior art. | major | yes | `05_related_work_and_positioning.tex`; bibliography | novelty audit source corpus | inadequate | Add Sen replies, Gibbard, Kelly, Blau, Gardenfors, Sugden, Pattanaik/Suzumura, AFP/formalization records. | no | yes |
| Standalone venue fit is not demonstrated. | major | yes | whole manuscript | SCW/JAR/JAIR policy pages | absent | Add a sharper audience story and reduce repository-internal planning language. | no | yes |

## 6. Minor objections

| Reviewer objection | Severity | Correct? | Affected passage | Evidence | Current defense | Required repair | New theorem/experiment? | Blocks submission? |
|---|---|---|---|---|---|---|---|---|
| The title is long and overclaims "basis". | minor | yes | `papers/m2/main.tex` title | basis terminology audit | partly adequate | Shorten and prefer "factorization". | no | no |
| The abstract is dense and assumes repository layers too early. | minor | yes | abstract | editor persona | partly adequate | Define Proof layer and Witness/Audit layer in plainer terms. | no | no |
| `arbitrary voter type` could be read as infinite-electorate theory. | minor | partly | abstract; scope; definitions | Lean signature lacks `Fintype Voter` | adequate but fragile | Say "polymorphic over voter type; not a theory of infinite electorates." | no | no |
| DOI/release relation is easy to misunderstand. | minor | partly | appendix | `papers/m2/ZENODO.md` | adequate | Keep Zenodo/GitHub/post-release distinctions in final manuscript. | no | no |

## 7. Mandatory attacks A1-A20

| Attack | Severity | Correct? | Assessment and required repair |
|---|---|---|---|
| A1. Trivial proof refactoring | major | partly | O2/O3/O4 are close to the standard proof structure. The publishable part is the public Lean interface and theorem ladder. Repair by saying "known Sen contradiction, newly exposed as kernel-checked public obstruction objects." |
| A2. "Basis" overclaim | major | yes | Current safeguards exist, but title/abstract still invite a stronger reading. Replace or qualify "basis" everywhere prominent. |
| A3. "Canonical family" ambiguity | major | yes | "Canonical" can imply uniqueness. Remove unless a normal-form theorem is proved. |
| A4. Not actually an atlas-to-general bridge | major | yes | The generic theorem is semantic, not derived from CNF. The strongest accurate relation: Sen24 was discovery/audit context; O2/O3/O4 are shared semantic shapes; CNF artifacts do not lift. |
| A5. Transfer Contract rhetoric | major | yes | The theorem is the semantic bridge; the scope wall is a guarantee-boundary/audit policy; "Transfer Contract" is framing. Label each layer explicitly. |
| A6. Scope-wall triviality | major | partly | The 5-cycle is elementary. Its significance is claim discipline for artifact transfer, not mathematical depth. Present it as boundary hygiene. |
| A7. Unformalized negative proposition | major | partly | For SCW, prose witness may suffice; for JAR, unformalized boundary weakens the formal-methods claim. State not Lean-checked and avoid theorem-like overclaim. |
| A8. Arbitrary voter type misreading | minor | partly | Manuscript mostly says this is a repository-interface result. Add one explicit non-claim against infinite-electorate theory. |
| A9. Hidden assumptions in `MINLIB` | major | partly | Manuscript lists distinct rights holders and pair non-distinctness, but should spell out fixed rights assignment, ordered decisive pairs, strict preference use, unrestricted profile construction, finite alternatives, and match to Sen's minimal liberalism. |
| A10. Profile construction adequacy | minor | no | Manuscript already says at most two ranking types is not a literal two-voter theorem. Preserve this. |
| A11. Programmatic dependence on unpublished papers | major | yes | Evidence/Explanation/companion/Narrative language risks dependence. Make M2 self-contained and move future papers to limitations. |
| A12. Outdated program nomenclature | major | yes | Four-contract table conflicts with locked M1/M1.5/M2/M3/M4 spine. Required major revision. |
| A13. Contribution list inflation | major | partly | Some bullets are one theorem-factorization contribution split into subclaims. Combine or group under one verified-factorization contribution plus one artifact-boundary contribution. |
| A14. Related-work incompleteness | major | yes | Bibliography lacks enough Sen rights/proof-variant sources and formalization context. Expand before submission. |
| A15. Venue mismatch: SCW | major | partly | Topic fits SCW, but current draft is repository/formal-methods heavy. Need a social-choice-facing contribution statement. |
| A16. Venue mismatch: JAR | major | partly | Formalization may be too small for JAR unless reusable proof-engineering lessons are foregrounded. Scope-wall not formalized is a weakness. |
| A17. Duplicate or incremental publication risk | minor | partly | Zenodo/GitHub release is archival, not peer-reviewed prior publication. Overlap with M1/M1.5/M2.1 must be disclosed and differentiated. |
| A18. Theorem significance | major | yes | Main theorem is Sen's known theorem. Paper must claim verified factorization and artifact-boundary discipline instead. |
| A19. Reproducibility claims | minor | partly | Current appendix mostly distinguishes source snapshot, release assets, DOI docs, kernel theorem, and audit policy. Keep this exact discipline. |
| A20. Doctoral-scope compliance | major | yes | Current M2 does not claim Arrow or M4 completion, but old four-contract language should be aligned with locked spine. |

## 8. Claim-to-code consistency audit

| Claim | Code status | Consistency |
|---|---|---|
| C1 | `SenRightsWitness` exists in `ObstructionBasis.lean`. | consistent |
| C2 | `classify_raw_overlap` and `ClassifiedSenRightsWitness.kind` exist. | consistent |
| C3 | `support_card_eq_kind` exists in `ObstructionSoundness.lean`. | consistent |
| C4 | Shape-specific outcome constructors and soundness functions exist. | consistent |
| C5 | `sen_outcome_obstruction_of_UN_MINLIB` exists in `ObstructionBridge.lean`. | consistent |
| C6 | `sen_impossibility_from_obstruction_basis` and `sen_impossibility_lifts` exist. | consistent |
| C7 | Non-transfer is documented in boundary docs, not encoded as Lean theorem. | consistent if labeled text-first |
| C8 | Transfer Contract is a manuscript/audit framing, not a Lean declaration. | consistent only with explicit labeling |
| C9 | The theorem ladder is public through named declarations. | consistent |

## 9. Claim-to-literature consistency audit

The manuscript must acknowledge that Sen's theorem and the rights/Pareto
conflict are established mathematics. The inspected literature supports a
moderate novelty claim for public Lean factorization and formal interface, not
a high novelty claim for the O2/O3/O4 mathematical cases. The related-work
section should be expanded before submission.

## 10. Dissertation-scope consistency audit

M2 remains within the locked dissertation scope:

- Sen-centered semantic bridge: yes.
- Arrow exclusion: respected.
- CNF/LRAT/atlas/repair family lift: explicitly not claimed.
- M3 completion: not claimed.
- M4 completion: not claimed.

Required correction: replace or reconcile the four-contract nomenclature with
the locked M1/M1.5/M2/M3/M4 spine.

## 11. Self-containment audit

M2 is not yet self-contained enough for external referees. It depends too much
on repository program terms such as Evidence Contract, Explanation Contract,
companion paper, and later Normative Contract. A revised standalone version
should define only the layers needed for M2 and move program dependencies to a
short "relation to repository program" paragraph.

## 12. Minimum viable revision package

| Addition or change | Classification |
|---|---|
| Remove or qualify prominent `basis` language. | required |
| Remove `canonical` unless explicitly defined as non-unique. | required |
| Separate known social-choice mathematics from Lean/interface novelty. | required |
| Rewrite finite-atlas relationship: discovery/audit context, not formal premise. | required |
| Label Transfer Contract as framing plus theorem/audit-policy components. | required |
| Replace stale four-contract nomenclature with M1/M1.5/M2/M3/M4 scope. | required |
| Add missing Sen-specific rights literature and mechanized-social-choice references. | required |
| Reduce repository-internal forward pointers. | required |
| Clarify arbitrary voter type and profile construction. | required |
| Preserve exact DOI/tag/release distinctions. | required |

## 13. Strong revision package

| Addition or change | Classification |
|---|---|
| Formalize the 5-cycle short-cycle/non-acyclicity witness in Lean. | recommended |
| Add a compact theorem or lemma tying raw overlap branches to paper-facing O2/O3/O4 objects. | recommended |
| Provide a reusable abstract schema for proof-layer vs artifact-layer transfer. | optional |
| Add a second independent mechanized impossibility case study. | out of scope for M2 |
| Add new solver, CNF, LRAT, or atlas experiments. | out of scope |

## 14. Changes that must not be made

- Do not claim Sen's theorem is new.
- Do not claim O2/O3/O4 are minimal, unique, or irredundant.
- Do not claim the Sen24 CNF, LRAT, atlas, repair, MUS, or MCS artifacts lift.
- Do not broaden scope to Arrow or other impossibility families.
- Do not import M3 or M4 claims into M2.
- Do not change the archived tag, release, DOI, Lean theorem, manuscript
  boundary, or generated artifacts as part of this audit.

## 15. Adversarial verdict

Verdict: `PASS WITH MAJOR REVISION`.

Fatal objections: none.

Major objections: six clusters block immediate submission: novelty framing,
`basis`/`canonical` terminology, theorem-vs-policy labeling, stale program
nomenclature, related-work incompleteness, and venue-facing self-containment.

New theorem required: no for a minimum viable submission.

New experiment required: no.

M2 remains usable as the dissertation semantic bridge. The standalone paper
should not be submitted until the required revision package is completed.
