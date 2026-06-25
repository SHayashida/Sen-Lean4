# M2 Literature Novelty Audit

## 1. Audit identity

- Repository: `SHayashida/Sen-Lean4`
- Audit branch: `codex/m2-one-time-reviewer-audit`
- Audit date: 2026-06-26 Asia/Tokyo
- Baseline `origin/main`: `90feec20154fa4610634b0d8ec059f8e8c018169`
- Archived M2 tag: `papers-m2-v2-obstruction-bridge`
- Archived M2 commit: `d7e5fd1ac94ab18330951b5d9741585dddc5b43a`
- Version DOI: `10.5281/zenodo.20796920`
- Concept DOI: `10.5281/zenodo.20468649`

This is a reviewer audit, not a manuscript revision. No claim in this document
modifies the M2 manuscript, Lean code, bibliography, release, DOI record, or
paper-specific claim boundary.

## 2. Audited manuscript and code baseline

The audit inspected the M2 manuscript files under `papers/m2/`, the M2
bibliography, `papers/m2/CLAIM_BOUNDARY.md`, `papers/m2/REPRODUCIBILITY.md`,
`papers/m2/ZENODO.md`, `docs/m2_scope_wall.md`,
`docs/doctoral_scope_lock.md`, and `docs/research_program_current.md`.

The Lean bindings inspected were:

- `SocialChoiceAtlas/Sen/ObstructionBasis.lean`
- `SocialChoiceAtlas/Sen/ObstructionProfiles.lean`
- `SocialChoiceAtlas/Sen/ObstructionSoundness.lean`
- `SocialChoiceAtlas/Sen/ObstructionBridge.lean`
- `SocialChoiceAtlas/Sen/Lifting/ImpossibilityLift.lean`

The audited theorem chain is:

```text
MINLIB
-> SenRightsWitness
-> ClassifiedSenRightsWitness
-> SenOutcomeObstruction
-> not SocialAcyclic
```

The scope wall is text-first: it is not a Lean theorem.

## 3. Claim inventory C1-C9

| ID | Claim |
|---|---|
| C1 | `MINLIB` is exposed as a reusable `SenRightsWitness` interface |
| C2 | Every extracted witness admits an exhaustive O2/O3/O4 overlap classification |
| C3 | O2/O3/O4 have exact support cardinalities 2/3/4 |
| C4 | O2 yields strict conflict, O3 a 3-cycle, and O4 a 4-cycle |
| C5 | `UN + MINLIB` yields `SenOutcomeObstruction` for arbitrary voter type and finite decidable alternative type |
| C6 | The obstruction refutes `SocialAcyclic`, with the legacy `Fin n / Fin m` theorem retained as a compatibility corollary |
| C7 | The general semantic theorem does not automatically lift the Sen24 CNF, LRAT, atlas, or repair artifacts |
| C8 | Proof-layer transfer and Witness/Audit-layer transfer must be recorded separately as a Transfer Contract |
| C9 | The overall theorem is factorized through public, kernel-checked intermediate obstruction objects rather than hidden case analysis |

No additional M2 claim is added by this audit.

## 4. Search protocol

Search cutoff: 2026-06-26.

Discovery methods used:

1. Scholarly index search through Crossref metadata queries and publisher
   article records.
2. Publisher/DOI verification through DOI, SpringerLink, University of Chicago
   Press/JSTOR-derived records when available, JAIR, and the Archive of Formal
   Proofs.
3. Backward and forward citation chaining from Sen 1970, Nipkow 2009, Tang and
   Lin 2009, Geist and Endriss 2011, Brandt and Geist 2016, Grandi and Endriss
   2013, and the M2 bibliography.

Search-result snippets, Wikipedia, blogs, and AI summaries were used only as
discovery aids and are not cited as evidence.

## 5. Query log

| Cluster | Queries and source paths |
|---|---|
| A. Sen liberal paradox | Crossref and publisher searches for `The Impossibility of a Paretian Liberal`, `Paretian liberal impossibility proof`, `minimal liberalism unanimity acyclicity`, `rights Pareto cycle social choice`, `A Pareto-Consistent Libertarian Claim`, `Liberal Values and Independence`, `Rights Games and Social Choice`, `Individual Rights and Social Evaluation`. |
| B. Finite obstructions | Searches for `finite obstruction social choice`, `forbidden substructure social welfare acyclicity`, `minimal obstruction liberal paradox`, `local witness general impossibility theorem`; backward chaining through Sen and automated social-choice papers. |
| C. Mechanized social choice | Searches for `Social Choice Theory in HOL`, `Archive of Formal Proofs social choice`, `Formalizing Arrow's theorem`, `Coq Arrow theorem social choice`, `Lean social choice theorem`. Official AFP and Springer records inspected. |
| D. Automated/SAT social choice | Crossref and publisher searches seeded by Tang and Lin 2009, Geist and Endriss 2011, Brandt and Geist 2016, plus `SAT social choice impossibility`, `computer-aided impossibility theorem`, `finite model search social choice`. |
| E. Lifting and finite-to-general transfer | Crossref and publisher searches for `Lifting Integrity Constraints in Binary Aggregation`, `small model property social choice`, `lifting theorem social choice`, `finite to general impossibility theorem`. |
| F. Proof artifacts | Searches and DOI verification for DRAT, LRAT, certified RAT verification, Lean 4, proof-producing solver trust boundary, and formal proof certificate abstraction boundary. |

## 6. Source corpus

Candidate primary-source pool inspected: 27 sources. Sources cited in this
audit: 23. Access date for all web-verified records: 2026-06-26.

| ID | Source | Venue/status | Identifier | Relevance to C1-C9 | Does not establish | Search path |
|---|---|---|---|---|---|---|
| S1 | Amartya K. Sen, "The Impossibility of a Paretian Liberal" (1970) | Journal of Political Economy; peer reviewed | DOI `10.1086/259614` | Original theorem; directly relevant to C4-C6 | Lean interface, O2/O3/O4 public formal objects, artifact scope wall | Crossref, backward seed |
| S2 | Sen, "The Impossibility of a Paretian Liberal: Reply" (1971) | Journal of Political Economy; peer reviewed | DOI `10.1086/259847` | Clarifies original debate | M2 factorization or mechanization | Crossref from S1 |
| S3 | Sen, "The Impossibility of a Paretian Liberal: Reply" (1973) | Journal of Political Economy; peer reviewed | DOI `10.1086/260083` | Further debate context | M2 artifacts or Lean formalization | Crossref from S1 |
| S4 | Allan Gibbard, "A Pareto-consistent libertarian claim" (1974) | Journal of Economic Theory; peer reviewed | DOI `10.1016/0022-0531(74)90111-2` | Rights/Pareto variants; close liberal paradox context | O2/O3/O4 basis or Lean bridge | Crossref and citation chain |
| S5 | Jerry S. Kelly, "Rights exercising and a Pareto-consistent libertarian claim" (1976) | Journal of Economic Theory; peer reviewed | DOI `10.1016/0022-0531(76)90071-5` | Liberal-rights response literature | M2 theorem factorization | Crossref from S4 |
| S6 | Julian H. Blau, "Liberal Values and Independence" (1975) | Review of Economic Studies; peer reviewed | DOI `10.2307/2296852` | Independence/nosiness response to Sen | Mechanized obstruction interface | Crossref |
| S7 | Peter Gardenfors, "Rights, Games and Social Choice" (1981) | Nous; peer reviewed | DOI `10.2307/2215437` | Rights/game-form alternative framing | O2/O3/O4 formal cardinality layer | Crossref |
| S8 | Robert Sugden, "Why be Consistent?" (1985) | Economica; peer reviewed | DOI `10.2307/2554418` | Consistency critique after Sen | M2 proof artifacts or Lean theorem | Crossref |
| S9 | Prasanta K. Pattanaik and Kotaro Suzumura, "Individual Rights and Social Evaluation" (1996) | Oxford Economic Papers; peer reviewed | DOI `10.1093/oxfordjournals.oep.a028565` | Rights/social evaluation conceptual framework | Repository-specific Transfer Contract | Crossref |
| S10 | Tobias Nipkow, "Social Choice Theory in HOL" (2009) | Journal of Automated Reasoning; peer reviewed | DOI `10.1007/s10817-009-9147-4` | Mechanized social choice; Arrow and Gibbard-Satterthwaite | Sen liberal paradox mechanization or O2/O3/O4 | Springer, AFP |
| S11 | Tobias Nipkow, "Arrow and Gibbard-Satterthwaite" (2008) | Archive of Formal Proofs; formal proof development, not journal peer review | Stable record `https://isa-afp.org/entries/ArrowImpossibilityGS.html` | Formal social-choice development | Sen MINLIB bridge | AFP search |
| S12 | Peter Gammie, "Some classical results in social choice theory" (2008) | Archive of Formal Proofs; formal proof development, not journal peer review | AFP record cited by S10 | Mechanized classical results | M2 Lean result or artifact scope wall | Backward from S10 |
| S13 | Freek Wiedijk, "Formalizing Arrow's theorem" (2009) | Sadhana; peer reviewed | Springer official record; DOI not verified in this audit | Mechanization context | Sen theorem or Lean | Backward from S10 |
| S14 | Pingzhong Tang and Fangzhen Lin, "Computer-aided proofs of Arrow's and other impossibility theorems" (2009) | Artificial Intelligence; peer reviewed | DOI `10.1016/j.artint.2009.02.005` | SAT/computer-aided finite impossibility | M2 semantic Lean bridge or artifact non-transfer theorem | M2 bibliography, Crossref |
| S15 | Christian Geist and Ulle Endriss, "Automated Search for Impossibility Theorems in Social Choice Theory" (2011) | JAIR; peer reviewed | DOI `10.1613/jair.3126` | Automated impossibility search | Sen O2/O3/O4 Lean interface | M2 bibliography |
| S16 | Felix Brandt and Christian Geist, "Finding Strategyproof Social Choice Functions via SAT Solving" (2016) | JAIR; peer reviewed | DOI `10.1613/jair.4959` | SAT social-choice search and scope of finite witnesses | M2 proof-layer transfer | M2 bibliography |
| S17 | Umberto Grandi and Ulle Endriss, "Lifting Integrity Constraints in Binary Aggregation" (2013) | Artificial Intelligence; peer reviewed | DOI `10.1016/j.artint.2013.05.001` | Lifting/finite-to-general methodology | Sen-specific MINLIB bridge | M2 bibliography |
| S18 | Johan de Kleer, "An assumption-based TMS" (1986) | Artificial Intelligence; peer reviewed | DOI `10.1016/0004-3702(86)90080-9` | Assumption management and diagnosis analogy | Proof-layer vs artifact-layer transfer contract | M2 bibliography |
| S19 | Nathan Wetzler, Marijn J. H. Heule, Warren A. Hunt, "DRAT-trim" (2014) | SAT 2014 LNCS; peer reviewed conference | DOI `10.1007/978-3-319-09284-3_31` | Proof-certificate checking | Social-choice theorem or M2 scope wall | M2 bibliography |
| S20 | Luis Cruz-Filipe et al., "Efficient Certified RAT Verification" (2017) | CADE 26 LNCS; peer reviewed conference | DOI `10.1007/978-3-319-63046-5_14` | Certified SAT proof checking | Sen-specific artifact transfer | M2 bibliography |
| S21 | Leonardo de Moura and Sebastian Ullrich, "The Lean 4 Theorem Prover and Programming Language" (2021) | CADE 28 LNCS; peer reviewed conference | DOI `10.1007/978-3-030-79876-5_37` | Lean kernel/proof assistant context | Social-choice novelty | M2 bibliography |
| S22 | John Geanakoplos, "Three brief proofs of Arrow's Impossibility Theorem" (2005) | Economic Theory; peer reviewed | DOI `10.1007/s00199-004-0556-7` | Proof-factorization precedent in social choice | Sen liberal paradox or artifact transfer | Backward from S10 |
| S23 | Mark A. Satterthwaite, "Strategy-proofness and Arrow's conditions" (1975) | Journal of Economic Theory; peer reviewed | DOI `10.1016/0022-0531(75)90050-2` | Classical social-choice impossibility context | Sen MINLIB basis | Backward from S10 |
| S24 | Allan Gibbard, "Manipulation of Voting Schemes" (1973) | Econometrica; peer reviewed | DOI `10.2307/1914083` | Classical impossibility context | M2 artifact claims | Backward from S10 |
| S25 | Davide Grossi and Gabriella Pigozzi, "Judgment Aggregation: A Primer" (2014) | Synthesis Lectures; scholarly monograph | DOI `10.1007/978-3-031-01568-7` | Aggregation/lifting context | Sen-specific bridge | Crossref |
| S26 | Brandt, Conitzer, Endriss, Lang, Procaccia, eds., "Handbook of Computational Social Choice" (2016) | Cambridge University Press; scholarly book | ISBN record; DOI not used | Computational social-choice background | Specific M2 theorem | Citation chain |
| S27 | JAIR, Springer SCW, and Springer JAR current author/aims pages (2026 access) | Official venue policy records | Stable journal pages | Venue fit only | Literature novelty | Official venue search |

## 7. Sen-proof comparison

The core social-choice theorem in M2 is not new mathematics. Sen 1970 already
establishes the conflict among unrestricted domain, Pareto, and minimal
liberalism, and the reply papers and rights literature show that the theorem
has long been analyzed through decisive rights, Pareto conflict, and consistency
conditions.

The M2 O2/O3/O4 family is best read as a proof-factorization of the familiar
Sen contradiction. The observed cases are mathematically elementary: identical
decisive-pair support gives a two-alternative strict conflict; one endpoint
overlap gives a three-alternative cycle; disjoint supports give a
four-alternative cycle. The search did not find a prior source using the exact
public O2/O3/O4 names with Lean-checked support-cardinality theorems, but it
also did not establish that no prior proof has used an equivalent implicit case
split. Different notation must not be treated as different mathematics.

Conclusion: C2-C6 should not be sold as a new Sen theorem. Their defensible
novelty is the public, kernel-checked factorization and exact interface.

## 8. Mechanized-social-choice comparison

Mechanized social choice is established prior art. Nipkow 2009 and the AFP
entry formalize Arrow and derive Gibbard-Satterthwaite in Isabelle/HOL. The
Springer record states that the article presents HOL formalizations of two
Geanakoplos proofs and derives Gibbard-Satterthwaite. The AFP entry records a
formal proof development for Arrow and Gibbard-Satterthwaite.

The search did not verify a prior Lean or Isabelle/Rocq mechanization of Sen's
liberal paradox with a reusable `MINLIB` witness interface and O2/O3/O4
obstruction object. That supports a cautious claim of formal-interface novelty,
not a proof that Sen has never been mechanized.

Conclusion: C1, C5, C6, and C9 have moderate mechanization/interface novelty
within this repository and likely within the inspected mechanized social-choice
corpus. Confidence is medium, not high, because the search did not exhaust all
local proof-assistant libraries and unpublished repositories.

## 9. SAT/lifting/artifact comparison

Automated finite social-choice search is established prior art through Tang and
Lin 2009, Geist and Endriss 2011, and Brandt and Geist 2016. Lifting questions
are established in aggregation by Grandi and Endriss 2013. Certified SAT
checking is established by DRAT/LRAT/RAT work such as Wetzler et al. 2014 and
Cruz-Filipe et al. 2017.

M2 does not add a SAT solver, a new proof-certificate format, or a family CNF
certificate. Its artifact-side contribution is methodological: record that a
kernel-checked semantic theorem and a finite CNF/LRAT witness live at different
layers and do not transfer together without a separate encoding contract. The
general idea that artifacts have trust boundaries is prior art. The specific
repository-local Transfer Contract wording appears to be a new framing, not a
new theorem.

## 10. Claim-by-claim novelty matrix

| Claim | Primary label | Mathematical novelty | Mechanization novelty | Interface/factorization novelty | Methodological novelty | Confidence |
|---|---|---|---|---|---|---|
| C1 | NEW-FORMAL-INTERFACE | none | moderate | high | low | medium |
| C2 | KNOWN-IDEA / NEW-PUBLIC-FACTORIZATION | low | moderate | moderate | low | medium |
| C3 | KNOWN-IDEA / NEW-PUBLIC-FACTORIZATION | low | moderate | moderate | low | medium |
| C4 | KNOWN-MATHEMATICS / NEW-MECHANIZATION | none | moderate | moderate | low | high |
| C5 | KNOWN-MATHEMATICS / NEW-MECHANIZATION | none | moderate | moderate | low | high |
| C6 | KNOWN-MATHEMATICS / NEW-MECHANIZATION | none | moderate | low | low | high |
| C7 | NEW-METHODOLOGICAL-FRAMING | low | none | low | moderate | medium |
| C8 | NEW-METHODOLOGICAL-FRAMING | none | none | moderate | moderate | medium |
| C9 | KNOWN-IDEA / NEW-PUBLIC-FACTORIZATION | none | moderate | high | low | medium |

## 11. Closest-prior-work matrix

| M2 claim | Closest source | Prior source establishes | M2 adds | Residual overlap risk | Safe wording |
|---|---|---|---|---|---|
| C1 | Sen 1970; rights literature S4-S9 | Decisive rights and minimal liberalism | Lean `SenRightsWitness` interface | Some prior formalization may package similar data | "We expose MINLIB as a reusable Lean witness interface." |
| C2 | Sen 1970 and proof variants | Contradiction from rights/Pareto profiles | Public O2/O3/O4 classifier | Equivalent case splits may be standard | "We factor the standard contradiction through an explicit O2/O3/O4 classifier." |
| C3 | Elementary finite-set reasoning | Support sizes are implicit in pair overlap | Kernel-checked cardinality theorem | Low mathematical novelty | "We kernel-check exact support cardinalities." |
| C4 | Sen 1970 | Conflict/cycle contradiction | Shape-specific Lean soundness | Very high overlap mathematically | "The known contradiction is reconstructed through shape-specific soundness lemmas." |
| C5 | Sen 1970 | General impossibility under Sen assumptions | Polymorphic Lean theorem over arbitrary voter type and finite alternatives | Could be close to a prior proof-assistant version if found | "The semantic theorem is kernel-checked in Lean over the repository interface." |
| C6 | Sen 1970; Nipkow 2009 as mechanization precedent | Impossibility theorem and formalization genre | Compatibility corollary retained | The theorem itself is known | "The legacy finite theorem is retained as an API-compatible corollary." |
| C7 | Tang/Lin; Geist/Endriss; Brandt/Geist; DRAT/LRAT work | Finite artifacts and proof certificates have scoped meaning | Explicit non-transfer of Sen24 CNF/LRAT/atlas/repair artifacts | General boundary idea is known | "The Sen24 artifact family is not lifted by the semantic theorem." |
| C8 | Certified proof and assurance-boundary literature | Artifacts require trust boundaries | Repository-local Transfer Contract split | Could be perceived as rhetoric | "We record a layer-level transfer contract, not a separate theorem." |
| C9 | Geanakoplos/Nipkow proof-factorization precedents | Public proof organization is valuable | Sen-specific obstruction objects in Lean | Factorization itself is not new methodology | "We make the intermediate obstruction objects public and kernel-checked." |

## 12. Negative-search limitations

- The search was serious but not exhaustive over every language, preprint
  server, local Lean/Rocq/Isabelle repository, or unpublished dissertation.
- Google Scholar-style forward citation data was used only as a discovery
  route, not as evidence.
- No accessible source was found that directly matches the exact M2
  combination: Sen MINLIB witness extraction, O2/O3/O4 public Lean objects,
  exact support cardinalities, and a Proof-vs-Witness/Audit Transfer Contract.
- This absence supports only `PLAUSIBLY-NOVEL-BUT-NOT-ESTABLISHED` for the
  exact combination. It does not prove absence of prior art.

## 13. Safe novelty language

Title:

> A Kernel-Checked Obstruction Factorization for Sen's Liberal Paradox and Its
> Artifact Boundary

Abstract novelty sentence:

> We mechanize Sen's known liberal-paradox contradiction through public Lean
> obstruction objects and record the boundary between semantic proof transfer
> and finite CNF artifact transfer.

Introduction one-sentence result:

> For Sen's liberal paradox, the semantic `UN + MINLIB` argument factors in
> Lean through O2/O3/O4 obstruction shapes, while the Sen24 CNF/LRAT artifact
> remains scoped to its audited short-cycle encoding.

Contribution list:

> The contribution is the verified interface and factorization, not a new
> social-choice impossibility theorem: witness extraction, overlap
> classification, shape soundness, generic Lean bridge, compatibility
> corollary, and explicit artifact non-transfer boundary.

Related-work novelty paragraph:

> Prior work establishes Sen's theorem, mechanized social choice for Arrow and
> Gibbard-Satterthwaite, SAT-based finite social-choice search, lifting in
> aggregation, and certified SAT proof checking. M2's contribution is narrower:
> a Lean-checked Sen-specific obstruction factorization plus a disciplined
> statement that the semantic theorem does not transport the Sen24 CNF witness.

## 14. Unsafe novelty language

Do not write:

- "We prove a new social-choice impossibility theorem."
- "The O2/O3/O4 family is a minimal, unique, or irredundant basis."
- "No prior work has considered these cases."
- "The Sen24 atlas lifts to the general theorem."
- "The Transfer Contract is a theorem of artifact transport."
- "Formalization alone establishes the paper's novelty."
- "The arbitrary voter type is a theory of infinite electorates."
- "The M2 result completes a multi-theorem-family bridge theory."

## 15. Overall novelty verdict

Verdict: `MODERATE`.

The mathematics is substantially known: the central impossibility result is
Sen's theorem, and the O2/O3/O4 branches are best treated as an explicit
classification of standard overlap possibilities rather than new social-choice
mathematics. The formal contribution is stronger: the inspected corpus did not
show a prior Lean-checked Sen liberal-paradox factorization through public
rights-witness and obstruction objects. The methodological contribution is
defensible but must be framed as claim discipline and artifact-boundary
engineering, not as a new transfer theorem for CNF artifacts.

M2 is therefore potentially publishable only if the manuscript foregrounds
verified factorization and artifact-boundary discipline, and weakens language
that suggests mathematical novelty of Sen's theorem, uniqueness of a basis, or
automatic atlas-to-general transfer.

## 16. References

- Sen, Amartya K. "The Impossibility of a Paretian Liberal." Journal of
  Political Economy 78(1), 152-157, 1970. DOI: `10.1086/259614`.
- Sen, Amartya K. "The Impossibility of a Paretian Liberal: Reply." Journal of
  Political Economy, 1971. DOI: `10.1086/259847`.
- Sen, Amartya K. "The Impossibility of a Paretian Liberal: Reply." Journal of
  Political Economy, 1973. DOI: `10.1086/260083`.
- Gibbard, Allan. "A Pareto-consistent libertarian claim." Journal of Economic
  Theory, 1974. DOI: `10.1016/0022-0531(74)90111-2`.
- Kelly, Jerry S. "Rights exercising and a Pareto-consistent libertarian
  claim." Journal of Economic Theory, 1976. DOI:
  `10.1016/0022-0531(76)90071-5`.
- Blau, Julian H. "Liberal Values and Independence." Review of Economic
  Studies, 1975. DOI: `10.2307/2296852`.
- Gardenfors, Peter. "Rights, Games and Social Choice." Nous, 1981. DOI:
  `10.2307/2215437`.
- Sugden, Robert. "Why be Consistent? A Critical Analysis of Consistency
  Requirements in Choice Theory." Economica, 1985. DOI: `10.2307/2554418`.
- Pattanaik, Prasanta K., and Kotaro Suzumura. "Individual Rights and Social
  Evaluation: A Conceptual Framework." Oxford Economic Papers, 1996. DOI:
  `10.1093/oxfordjournals.oep.a028565`.
- Nipkow, Tobias. "Social Choice Theory in HOL." Journal of Automated
  Reasoning 43, 289-304, 2009. DOI: `10.1007/s10817-009-9147-4`.
- Nipkow, Tobias. "Arrow and Gibbard-Satterthwaite." Archive of Formal Proofs,
  2008. `https://isa-afp.org/entries/ArrowImpossibilityGS.html`.
- Wiedijk, Freek. "Formalizing Arrow's theorem." Sadhana, 2009.
- Tang, Pingzhong, and Fangzhen Lin. "Computer-aided proofs of Arrow's and
  other impossibility theorems." Artificial Intelligence, 2009. DOI:
  `10.1016/j.artint.2009.02.005`.
- Geist, Christian, and Ulle Endriss. "Automated Search for Impossibility
  Theorems in Social Choice Theory: Ranking Sets of Objects." JAIR, 2011. DOI:
  `10.1613/jair.3126`.
- Brandt, Felix, and Christian Geist. "Finding Strategyproof Social Choice
  Functions via SAT Solving." JAIR, 2016. DOI: `10.1613/jair.4959`.
- Grandi, Umberto, and Ulle Endriss. "Lifting Integrity Constraints in Binary
  Aggregation." Artificial Intelligence, 2013. DOI:
  `10.1016/j.artint.2013.05.001`.
- de Kleer, Johan. "An assumption-based TMS." Artificial Intelligence, 1986.
  DOI: `10.1016/0004-3702(86)90080-9`.
- Wetzler, Nathan, Marijn J. H. Heule, and Warren A. Hunt. "DRAT-trim:
  Efficient Checking and Trimming Using Expressive Clausal Proofs." SAT 2014.
  DOI: `10.1007/978-3-319-09284-3_31`.
- Cruz-Filipe, Luis, Marijn J. H. Heule, Warren A. Hunt Jr., Matt Kaufmann,
  and Peter Schneider-Kamp. "Efficient Certified RAT Verification." CADE 26,
  2017. DOI: `10.1007/978-3-319-63046-5_14`.
- de Moura, Leonardo, and Sebastian Ullrich. "The Lean 4 Theorem Prover and
  Programming Language." CADE 28, 2021. DOI:
  `10.1007/978-3-030-79876-5_37`.
- Geanakoplos, John. "Three brief proofs of Arrow's Impossibility Theorem."
  Economic Theory, 2005. DOI: `10.1007/s00199-004-0556-7`.
- Satterthwaite, Mark A. "Strategy-proofness and Arrow's conditions:
  Existence and correspondence theorems for voting procedures and social
  welfare functions." Journal of Economic Theory, 1975. DOI:
  `10.1016/0022-0531(75)90050-2`.
- Gibbard, Allan. "Manipulation of Voting Schemes: A General Result."
  Econometrica, 1973. DOI: `10.2307/1914083`.
