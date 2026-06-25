# Current Research Program

## Status Header

- As of: 2026-06-24
- Repository: SHayashida/Sen-Lean4
- Primary application scope: Sen liberal paradox
- Abstract theorem scope: finite-set reportability interfaces
- Cross-theorem social-choice generality: not claimed
- Arrow: deferred beyond the current dissertation program

## Current North-Star Claim

A verified impossibility result does not automatically license generalization,
repair, reporting, or institutional action. Each transition requires an
explicit contract and a preservation theorem.

This is the unifying proposition for the research program as a whole. It is
not, by itself, a novelty claim for any single paper.

## Typed Transition Architecture

The current program is organized around five typed stages:

1. Finite Evidence
2. General Semantic Claim
3. Raw Repair Explanation
4. Grouped Repair Report
5. Institutional Action

The four transition boundaries are:

| Boundary | Current status | Required justification / contract |
|---|---|---|
| Finite artifact evidence <-> general semantics | A common bounded semantic-obstruction vocabulary is established; artifact-driven transfer is not established. | Encoding correctness and an artifact-to-semantics bridge. |
| General semantic impossibility -> raw repair | Non-entailment / representation dependence is established; no general positive repair transport theorem is claimed. | Repair semantics, editable-lever choice, and representation contract. |
| Raw repair -> grouped report | Abstract reportability theorems are established; Candidate B has an artifact-defined instantiation. | `ResidualFaithfulness` and `RepairAtomicity` or `GroupSoundness`, with stated monotonicity conditions for exactness. |
| Grouped report -> institutional action | Open / M4 design stage. | Warrant, authority, delegation, scope, abstention, and appeal conditions. |

For M2, "bridge established" must always be qualified by layer. M2 is not an
artifact-driven theorem from the Sen24 CNF, LRAT, or atlas. The generic theorem
is proved semantically through the O2/O3/O4 obstruction family. Sen24 and the
generic theorem share bounded semantic obstruction shapes, but the Sen24
artifact is not a formal premise of the generic theorem.

The program treats the following as explicit non-implications:

- Valid finite evidence does not automatically imply a general theorem.
- Valid impossibility does not determine canonical raw repair.
- Valid raw repair does not automatically determine a valid grouped report.
- Valid report does not automatically authorize institutional action.

## Module Map

### M1 - Finite Evidence Diagnosability

Current status:

- Sen24 fixed finite atlas.
- Proof / Audit / Witness / Assumption separation.
- SAT frontier, validated witnesses, committed LRAT references, and repair
  triangulation.
- No new Sen theorem claim.
- No end-to-end semantic-to-Python-CNF correctness theorem claim.

M1 remains the audited finite base-case layer. Its CNF, LRAT, atlas, and repair
artifacts are scoped to Sen24 unless a separate bridge is established.

### M1.5 - Raw Repair Non-Canonicity

Current status:

- Bundled versus split liberalism encodings.
- Clause-multiset equivalence.
- Raw lever-level minimal repair families are not invariant.
- Finite witness validity does not settle repair presentation.

M1.5 isolates a repair-representation issue: even when two encodings are
controlled enough to compare, the raw repair family can depend on how the
axiom is presented.

### M2 - Finite Semantic Obstruction Bridge

Current status:

- Generic `UN + MINLIB` instance.
- Classified bounded obstruction family O2/O3/O4.
- Exact support sizes 2/3/4.
- Outcomes: strict conflict / 3-cycle / 4-cycle.
- Generic impossibility derived from the obstruction family.
- Legacy `sen_impossibility_lifts` is a compatibility corollary.

In M2, "basis" means only a complete finite generating family of semantic
obstruction shapes.

It does not mean:

- minimality,
- irredundancy,
- uniqueness.

The M2 scope wall is:

- Semantic Proof-layer bridge: established.
- CNF bridge: not established.
- LRAT bridge: not established.
- Atlas bridge: not established.
- Repair/MCS bridge: not established.
- The Sen24 artifact is not a formal premise of the generic theorem.

### M2.1 - Dimension-Sensitive Representation Boundary

Current status:

- In the tested neighboring case `(2,5)`, alternative expansion preserves
  clause-multiset equivalence under the fixed two-voter witness basis and
  preserves raw repair divergence.
- In the tested neighboring case `(3,4)`, the compared bundled and
  pair-selector split packages are both UNSAT, but clause-multiset equivalence
  fails because voter-pair selection and role-specific selector machinery add
  unmatched structure.
- No repair enumeration was authorized for the `(3,4)` `sat_equiv_only`
  comparison.
- No theorem for arbitrary alternative expansion, arbitrary voter expansion, or
  arbitrary `(n,m)` is claimed.
- M2.1 is a two-case directional boundary result, not a full repair-transfer
  theorem.

M2.1 explains, for the tested `(2,5)` and `(3,4)` neighboring cases, where the
M1.5 representation witness transfers cleanly and where the clause-multiset
control stops.

### M3 - Grouped Reportability

Current status:

- Residual Faithfulness.
- Repair Atomicity.
- Group Soundness.
- Monotonicity.
- Grouped correctness.
- Characterization / converse under the stated assumptions.
- Candidate B as the finite application.
- Raw non-canonicity and grouped correctness are compatible.

M3 studies when raw repair information may be grouped into a report without
misrepresenting the underlying repair semantics.

Guarantee boundary:

- The abstract finite-set reportability theorem core is kernel-checked in
  Lean.
- The theorem core is independent of CNF solving.
- Candidate B is an artifact-backed, artifact-defined instantiation.
- Candidate B is not thereby upgraded to a semantic social-choice contract, a
  Lean-level encoding-correctness theorem, or a family-scale reportability
  theorem.
- Raw repair non-canonicity remains true; M3 recovers grouped correctness only
  relative to an explicit contract satisfying the relevant conditions.
- M3-A does not apply to the non-atomic Candidate B liberalism block.
- Candidate B is recovered through the M3-B / `GroupSoundness` route.
- The M3-C characterization is conditional on the stated deletion-monotonicity
  and residual-faithfulness regime.

### M4 - Institutional Warrant

Current status: design stage, not completed.

Target question:

> Under what conditions may a valid grouped repair report be used to warrant an
> institutional action?

Candidate notions:

- Authority.
- Delegation.
- Action scope.
- Warrant preservation.
- Abstention / escalation.
- Override / appeal.

No completed M4 theorem is claimed.

## Change From The Original Plan

| Original plan | Current status | Reason |
|---|---|---|
| Direct Sen24 UNSAT lifting | Replaced by semantic obstruction bridge | The generic result is proved through O2/O3/O4 semantic obstruction shapes, not by treating the Sen24 CNF artifact as a formal premise. |
| Family-level MUS/MCS lifting | Not established | Repair/MCS bridge from Sen24 artifacts to a family remains outside the claim boundary. |
| Generic repair geometry | Made contract-relative by M1.5/M3 | Raw repairs are representation-sensitive, and grouped reports require separate reportability conditions. |
| Arrow finite atlas | Deferred beyond dissertation scope | Current scope is Sen liberal paradox only. |
| Sen-to-Arrow comparison paper | Deferred | Cross-theorem generality is not claimed in the current program. |
| AI repair proposer / DSL | Deferred to application phase | The current program first fixes evidence, bridge, repair, reportability, and warrant contracts. |
| DAO / AI-agent committee application | Deferred | Field application follows only after the warrant layer is designed. |
| Institutional design | Reformulated as warrant preservation | The M4 question is when a grouped report can authorize action, not generic institutional design. |

## Dissertation Spine

The current five-part structure is:

- M1: finite evidence diagnosability.
- M1.5: raw repair non-canonicity.
- M2: finite semantic obstruction basis to general Sen theorem.
- M3: grouped repair reportability.
- M4: institutional warrant.

One-sentence dissertation thesis:

> Machine-checked correctness is not by itself a license to generalize, repair,
> report, or act.

## Publication Strategy

Current strategy, without acceptance claims:

- WINE 2026 primary candidate: integrated M1.5 + M3 paper.
- M2: separate finite-semantic-obstruction bridge paper.
- M1: auditable finite-evidence / formal-methods paper.
- M2.1: boundary paper or appendix depending on publication strategy.
- M4: dissertation culmination / later standalone paper, pending theorem design.

Conference deadlines and acceptance probabilities are intentionally excluded
from this canonical research map.

## Deferred Program

The following are post-current-program work:

- Arrow and other impossibility theorem families.
- Cross-theorem bridge theory.
- Artifact-driven finite-to-general bridge.
- Family-level repair/MCS transfer.
- Verified general-purpose CNF generator.
- Institution-design DSL.
- LLM repair proposer.
- DAO / AI-agent committee field application.
- Dynamic ripple-effect analysis.
