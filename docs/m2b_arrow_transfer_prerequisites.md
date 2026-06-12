# M2b Arrow Transfer Prerequisites

## 1. Why Arrow comes after M3, and in which vocabulary

M3 has established the following reportability framework:

- M3-A: an atomic syntactic sufficient condition;
- M3-B: a non-atomic group-soundness sufficient condition;
- M3-C: candidate exactness under deletion-monotone reference contracts;
- Candidate B: an artifact-backed instantiation on the same witness that exposed the M1.5 raw reportability gap.

Arrow enters only after this framework because it tests a different question: whether the residuals to be reported have first been legitimized at the truth/certificate level.

Arrow is a truth/certificate prerequisite before repair/report comparison.

Following the M2 Transfer Contract, "transfer" is not a single claim. It splits into:

1. Proof-layer transfer: transfer of the semantic or mathematical argument.
2. Witness/Audit-layer transfer: transfer of concrete encodings, artifacts, and evidence packages.

The Witness/Audit layer never auto-transfers. This document therefore records what the Proof layer may legitimize for Arrow and what remains blocked at the Witness/Audit layer. The Repair/Report layer becomes available only after those prior obligations are discharged within a declared scope.

## 2. Why Arrow is not merely a second example

Sen/Candidate B operated inside an explicitly scoped and audited artifact-defined contract. Arrow raises a prior question: whether finite witnesses or finite certificates legitimately represent the intended family-level or unrestricted Arrow claim.

General syntactic finite-to-general transfer in the individual dimension is not guaranteed for Arrow-type settings. The repository's Row 2, or "reason Y," records this caution in connection with Grandi-Endriss-style finite-model limitations. This does not contradict theorem-specific transfer. Tang and Lin (2009) are a candidate Proof-layer anchor because they are reported to provide manual induction lemmas reducing Arrow's impossibility for general finite `(n,m)` to a small base case. The repository verifies the bibliographic entry but not the exact theorem statement or scope:

> to be verified: Tang-Lin theorem-specific apex transfer statement.

The two positions therefore coexist: there may be no generic transfer scheme, while a theorem-specific transfer proof may exist for the impossibility apex.

M3 does not supply finite-to-general transfer. M3 governs reportability only after the relevant reference residuals are in scope.

## 3. The per-residual transfer obligation and the lattice asymmetry

M3 consumes the entire deletion lattice:

```text
Psi(T) for every T subseteq I
```

It does not consume only the fully active impossibility residual. For M3 purposes, "Arrow transfer" is therefore a per-residual obligation.

### UNSAT apex

The fully active residual, where all Arrow contract atoms are active, is the impossibility apex.

Family-level legitimacy for this apex may route through:

- theorem-specific transfer, such as verified Tang-Lin induction lemmas; or
- a kernel-checked Proof-layer lift, if available.

This concerns the UNSAT apex only.

### SAT residuals

Proper residuals, where one or more contract atoms have been deleted, are different.

Their family-level legitimacy is not established by the same apex transfer. For each SAT residual intended for family-level use, one must provide either:

- a uniform rule construction over the target family; or
- an explicit finite-scope restriction.

Candidate routes, not established claims, include:

- deleting non-dictatorship may be witnessed by dictatorial rules;
- deleting IIA may be witnessed by positional rules such as Borda;
- deleting transitivity or social rationality may require a separate construction;
- domain restrictions require their own scope statement.

Conflating apex transfer with residual-lattice transfer is the primary overclaim risk for Arrow. This document exists to prevent that error.

## 4. Target Arrow claim classes

| Claim level | Meaning | M3 consumption status |
| --- | --- | --- |
| finite atlas fact | status of a specific finite encoding | consumable only as finite-scope residual |
| family-level finite-n/m claim | transfer across a declared finite family | consumable only if per-residual transfer is proven or explicitly scoped |
| unrestricted Arrow claim | unrestricted social choice theorem | not consumable without a separate theorem |

The expected near-term milestone is not an unrestricted Arrow instantiation. It is a finite-scope artifact-defined Arrow contract at a declared base case, replicating the Candidate B methodology. Family-level consumption is gated by the per-residual obligations in Section 3.

## 5. Candidate finite base cases and proof-layer anchors

Repository inspection verified bibliographic entries for Tang and Lin (2009), Grandi and Endriss (2013), and Nipkow (2009), including in `papers/m2_1/bib/references.bib`. It did not verify the exact Tang-Lin induction theorem statement, locate an Arrow artifact, locate an M2b Option A-2 encoding plan, or locate a Lean/mathlib Arrow formalization. The table preserves those limits.

| Candidate | Layer | Source / repo path | Status | Transfer status | Allowed M3 use |
| --- | --- | --- | --- | --- | --- |
| Tang-Lin small base certificate, e.g. `(2,3)` | Witness/Audit | Tang & Lin 2009 bibliography verified at `papers/m2_1/bib/references.bib`; certificate path not found in current repo | finite artifact not implemented; base-case details to be verified | apex transfer only if theorem statement is verified; per-residual transfer unresolved | finite-scope residual only unless separately justified |
| Tang-Lin induction lemmas | Proof | Tang & Lin 2009 bibliography verified at `papers/m2_1/bib/references.bib`; exact theorem statement to be verified | theorem-specific Proof-layer candidate | apex only | may legitimize UNSAT apex, pending verified statement scope |
| Nipkow mechanized Arrow | Proof | Nipkow 2009 bibliography verified at `papers/m2_1/bib/references.bib`; related-work mention at `papers/m2_1/sections/06_related_work.tex` | mechanized HOL proof candidate; exact scope to be verified | apex only unless residual lattice is covered | Proof-layer anchor candidate |
| Lean/mathlib Arrow formalization | Proof | path not found in current repo | not found in current repo | to be verified | potential kernel-checked apex anchor only if confirmed |
| Repo M2b Option A-2 encoding plan | Witness/Audit | path not found in current repo | not found; not implemented | none yet | no M3 use yet |
| finite Arrow atlas base case | Witness/Audit | path not found in current repo | not implemented | finite-only | finite-scope only |

A row may be transfer-proven for the apex while remaining unresolved for the residual lattice. Apex transfer and per-residual transfer must not be collapsed into one claim. Without an artifact, a Witness/Audit-layer candidate remains not implemented.

## 6. Residual contract candidates

Possible Arrow-side contract atoms are candidates only:

| Candidate atom | Contract atom? | Implementation lever? | Anticipated block structure | Status |
| --- | --- | --- | --- | --- |
| Pareto / unanimity | candidate | TBD | possible agent-conjunction bundle/split | unresolved |
| IIA | candidate | TBD | possible double-universal bundle/split over agents and situation pairs | unresolved |
| non-dictatorship | candidate | TBD | possible selector / witness-selection machinery | unresolved |
| transitivity / social rationality | candidate | TBD | possible cycle-constraint bundle/split | unresolved |
| domain restriction | candidate if used | TBD | scope-defining rather than repair atom unless declared | unresolved |

Known bundled-vs-split candidates should be tied to actual repository notes. No Arrow-specific path was found during this inspection:

> identified in prior program discussion; repository path to be recorded.

No atom is reportable merely because it appears in an implementation. A reportable atom must be declared by the contract.

## 7. Encoding-sensitivity risks

Likely Arrow-side representation risks include:

- IIA double universal quantification;
- unanimity / Pareto agent conjunction;
- non-dictatorship witness selection;
- transitivity cycle constraints;
- selector variables introduced by voter expansion;
- alternative-dimension changes;
- voter-dimension changes.

These are Arrow-side analogues of the Sen `minlib` bundled/split refinement. The M2.1 voter-dimension boundary, where selector machinery breaks clause-multiset protected comparison, is the concrete precedent for the non-dictatorship and voter-expansion rows.

These are risk candidates, not theorem claims. Non-canonicity must not be asserted without an artifact or proof.

## 8. Prerequisites before M3 can use Arrow

### Proof layer

1. Declare the Arrow target family.
2. For the UNSAT apex, prove or cite apex transfer with verified statement scope.
3. For each SAT residual intended for family-level use, supply a uniform rule witness or explicitly stop at finite scope.

### Witness/Audit layer

4. Declare the finite residual contract, artifact-defined first.
5. Establish the status of every finite residual by audited artifacts.
6. Establish residual faithfulness inside the declared scope.
7. Record `PsiDeletionMonotonicity`. It is expected for conjunctive axiom-deletion encodings, but it must be recorded, not assumed.

### Repair/Report layer

8. Only after the preceding obligations are satisfied may one test repair atomicity, `GroupSoundness`, or grouped invariance.

If transfer fails or remains unproven for any residual, the M3 claim must stop at finite-scope reportability for that residual.

## 9. What Arrow can show even if transfer fails

A failed or incomplete Arrow transfer is still useful.

It shows that M3's two-axis framework is doing real work:

- truth/certificate legitimacy must be established first;
- repair/report invariance cannot outrun the scope of the reference residuals.

If Arrow transfer remains finite-only, that is not a failure of M3. It is an example of M3 refusing to report beyond the certified scope.

## 10. Go / No-Go criteria for Arrow use in M3

### Go if

- the target family is explicit;
- the finite residual contract is explicit;
- residual status is artifact-backed or theorem-backed;
- transfer status is recorded for every residual;
- residual faithfulness is established inside the declared scope;
- `PsiDeletionMonotonicity` is recorded if used;
- reportability claims are limited to the certified scope.

### No-Go if

- a finite witness is silently treated as unrestricted Arrow;
- apex transfer is silently extended to the residual lattice;
- a finite SAT residual model is presented as a family-level possibility claim without a uniform rule witness or explicit finite-scope marking;
- implementation selectors determine reportable atoms without contract declaration;
- residual faithfulness is assumed beyond proven transfer scope;
- repair/report comparison is attempted before truth/certificate legitimacy is established;
- the Grandi-Endriss caution and the Tang-Lin induction are presented as contradictory rather than reconciled as generic-transfer caution versus theorem-specific apex transfer.

## 11. Relation to dissertation spine

M1.5 exposed the reportability gap. M3-A/B/C showed how reportability can be earned under explicit contract conditions. Candidate B demonstrated the theory on the same witness that exposed the gap.

Arrow is the next test of scope discipline. It asks whether the reference residuals themselves have enough transfer legitimacy to be used by M3.

The Arrow prerequisites instantiate, for a new theorem family, the same discipline that M2 established for Sen: transfer is layer-split, and every claim routes through a declared contract.

## 12. What this document does not do

- It does not implement Arrow.
- It does not run SAT.
- It does not claim unrestricted Arrow transfer.
- It does not instantiate M3-B on Arrow.
- It does not claim per-residual transfer.
- It does not introduce M4.
- It does not add AI-governance implementation material.
- It does not create a six-layer taxonomy.

## 13. Acceptance criteria

- Create exactly one file: `docs/m2b_arrow_transfer_prerequisites.md`.
- Make no code changes.
- Run no solvers.
- Create no new experiments.
- Frame Arrow as a prerequisite testbed, not as main M3 evidence.
- Include each required exact sentence exactly once.
- Use the layer-split vocabulary: Proof layer, Witness/Audit layer, and Repair/Report layer.
- State the per-residual transfer obligation and apex/residual asymmetry substantively in Section 3.
- Include the Grandi-Endriss / Tang-Lin reconciliation.
- Pre-seed the candidate table with the required entries.
- Mark every unverified source, theorem scope, and repository path explicitly.
- Do not fabricate citations or paths.
- State that M3 cannot supply finite-to-general transfer.
- Allow a finite-only stopping point without treating it as failure.
- Add no Arrow implementation, M4 implementation, DAO material, AI-governance implementation, or six-layer taxonomy.
