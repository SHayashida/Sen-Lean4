# M3 Paper Section Allocation

## 1. Purpose and Meta-Document Freeze

This document converts the completed M3 scaffolding into a paper outline. It does not introduce new claims. It assigns existing definitions, theorem skeletons, audits, and boundary documents to manuscript sections.

This is the final M3 meta/planning document. After this allocation, the project moves to Lean formalization and `papers/m3/` manuscript drafting.

Do not create another M3 scaffolding document unless a concrete proof, build, or reviewer issue requires it.

## 2. Target Format

M3 will be drafted as a standalone full paper under:

```text
papers/m3/
```

The dissertation-chapter adaptation will be done later.

Recommended target ladder:

- primary: a full research venue such as AAMAS or IJCAI;
- journal option: JAIR;
- workshop use: optional only for M1.5/M2.1 feedback, not the default target for M3.

M3 has a larger structure than M1.5: three theorem components, a characterization under monotone contracts, and an artifact-backed Candidate B instantiation. Therefore the default writing target is a full paper, not a short workshop note.

## 3. Core Thesis of M3

A valid impossibility certificate does not by itself determine how repairs may be reported. Repair reportability is a contract-relative property. Under explicit interface and soundness conditions, grouped repair reports can be canonical even when raw implementation repairs are not.

Candidate B is raw-noncanonical and contract-canonical at the same time.

M1.5 shows why reportability cannot be assumed; M3 shows how reportability can be earned.

## 4. Manuscript Section Map

| Paper section | Working title | Source scaffold | Main claim | Status |
| --- | --- | --- | --- | --- |
| 1 | Introduction: the reportability gap | `docs/m1_5_to_m3_transition.md` | M1.5 exposes raw repair non-canonicity; M3 asks when report-level canonicity can be earned | ready |
| 2 | Contracts, realizations, and repair reports | `docs/m3_reportability_contract.md` | Defines contract-relative reportability objects | ready |
| 3 | Atomic interfaces | `docs/m3_atomicity_theorem_skeleton.md` | M3-A: atomicity + residual faithfulness gives grouped invariance and raw transport | theorem skeleton; formalization pending |
| 4 | Non-atomic group-soundness | `docs/m3_nonatomic_group_soundness_skeleton.md` | M3-B: group-soundness + residual faithfulness gives grouped correctness | theorem skeleton; formalization pending |
| 5 | Exactness under monotone contracts | `docs/m3_nonatomic_group_soundness_skeleton.md` | M3-C: under Psi-deletion-monotonicity, grouped correctness implies GroupSoundness | candidate theorem; promotion pending |
| 6 | Candidate B audit | `docs/m3_candidate_b_group_soundness_audit_plan.md`; `docs/m3_candidate_b_group_soundness_audit_result.md` | Candidate B instantiates M3-B under an artifact-defined bundled contract | PASS |
| 7 | Related work and positioning | M1/M1.5/M2 references; diagnosis and MUS literature | Positions M3 against diagnosis, MUS granularity, and social-choice verification | needed |
| 8 | Scope and transfer boundary | `docs/m2b_arrow_transfer_prerequisites.md` | Arrow is a truth/certificate prerequisite before repair/report comparison | ready as boundary |
| 9 | Discussion | transition + all scaffolds | M3 separates raw non-canonicity from contract-level reportability | ready for drafting |

## 5. Lean Formalization Decision

The M3 main theorem layer should be Lean-formalized before or in parallel with the TeX manuscript.

Reasons:

- M3-A/B/C are finite-set transport theorems, not SAT/CNF formalizations.
- They should be formalizable at an abstract finite-set level.
- Kernel-checking turns the technical simplicity of the proofs into a strength: the paper's auditability claims are supported by formally checked theorem infrastructure.

Target formalization scope:

| Component | Lean target | Priority |
| --- | --- | --- |
| M3-A | finite-set theorem for `RepairAtomicity + ResidualFaithfulness => GroupedInvariance` and raw transport | required |
| M3-B | finite-set theorem for `GroupSoundness + ResidualFaithfulness => GroupedRep_C(E) = ContractRep(C)` | required |
| M3-C | converse under `PsiDeletionMonotonicity` | strongly recommended |
| Candidate B audit | not formalized in Lean; remains artifact-backed | no |
| SAT/CNF semantics | not formalized here | no |

If Lean formalization is deferred, the deferral must be explicitly justified in the manuscript plan and not silently treated as completed.

## 6. M3-C Promotion Checklist

M3-C must not remain a vague "candidate" in the final paper.

| Requirement | Status |
| --- | --- |
| Full prose proof written from the skeleton | pending |
| Converse proof checked for use of `PsiDeletionMonotonicity` only | pending |
| Residual faithfulness asymmetry stated correctly | pending |
| Non-monotone counterexample included as a remark | pending |
| Equivalence corollary stated with exact scope | pending |
| Lean formalization attempted or deferral justified | pending |

M3-C may be promoted from candidate theorem to theorem only after this checklist is satisfied.

## 7. Claim Discipline

This is the first of the two designated main-text tables.

| Claim | Allowed? | Required qualification |
| --- | --- | --- |
| M1.5 shows raw repair non-canonicity | yes | Candidate B / declared artifact scope |
| M3-A recovers Candidate B | no | M3-A does not apply to non-atomic split `minlib` |
| M3-B recovers report-level canonicity on Candidate B | yes | only under artifact-defined contract and verified `GroupSoundness` |
| Candidate B raw repairs become canonical | no | raw non-canonicity remains |
| `GroupSoundness` characterizes grouped correctness | yes | only for residually faithful realizations over `Psi`-deletion-monotone contracts |
| Atomicity is necessary | no | M3-A is a sufficient condition only |
| Raw transport holds under M3-B | no | raw transport is an M3-A result only |
| M3 results extend to family scale | no | Candidate B is artifact-defined / base-scope unless separately lifted |
| Arrow provides a second M3 example | no | Arrow is a prerequisite testbed unless per-residual transfer is established |
| Artifact-defined contract equals semantic/Lean contract | no | semantic/formal upgrading is a separate truth/certificate obligation |
| Encoding-granularity sensitivity of repairs is new by itself | no | M3's novelty is contract-relative reportability and exactness conditions |

## 8. Related Work Allocation

| Cluster | Role in M3 positioning |
| --- | --- |
| Model-based diagnosis / ATMS | background on explanations, assumptions, and repairs |
| MUS/MCS and repair enumeration | background; encoding granularity effects are not claimed as novel by themselves |
| High-level vs low-level explanations | positions contract-level reporting as a principled abstraction problem |
| Computational social choice SAT proofs | Tang-Lin, Geist-Endriss, Grandi-Endriss, Brandt-Geist, and related work |
| Formal verification of social choice | Nipkow/HOL, Lean theorem-proving context, and this project's M1/M2 line |
| M1/M1.5/M2 internal program | explains how M3 follows from reportability-gap and transfer-contract discipline |

The paper must not present "MUS changes under encoding granularity" as the primary novelty. That phenomenon is related to existing diagnosis/MUS literature. The M3 contribution is the contract-relative theory of reportability, the non-atomic group-soundness condition, the monotone-contract exactness result, and the Candidate B artifact-backed instantiation.

## 9. Figure and Table Plan

The manuscript will contain exactly three figures:

1. M1.5 to M3 spine: raw non-canonicity -> M3-A/B/C -> Candidate B grouped canonicity.
2. Two-axis framework: truth/certificate axis vs repair/report axis.
3. Candidate B grouping diagram: bundled `minlib` vs split `decisive_voter0`, `decisive_voter1`, with both grouping to `{minlib}`.

The manuscript will contain exactly two main-text tables:

1. The claim discipline table in Section 7 of this allocation.
2. The M3-A vs M3-B vs M3-C theorem comparison table below.

| Component | Interface condition | Other assumptions | Conclusion | Raw transport? | Current status |
| --- | --- | --- | --- | --- | --- |
| M3-A | `RepairAtomicity` | `ResidualFaithfulness` | grouped invariance through `ContractRep(C)` | yes, under the atom-induced bijection | theorem skeleton; formalization pending |
| M3-B | `GroupSoundness` permits non-atomic blocks | `ResidualFaithfulness` | single-realization grouped correctness and two-realization grouped invariance | no | theorem skeleton; formalization pending |
| M3-C | no atomicity requirement | `PsiDeletionMonotonicity` plus grouped correctness | `GroupSoundness` | no | promotion pending |

The atomicity dependency table from `docs/m3_atomicity_theorem_skeleton.md` should appear as a compact appendix table, not as a figure. Its purpose is to show precisely where atomicity is used and where M3-B replaces it with `GroupSoundness`.

All other tables in this allocation document are planning inventories or appendix candidates, not designated manuscript main-text tables.

## 10. Theorem Inventory

- M3-A: `RepairAtomicity + ResidualFaithfulness => GroupedInvariance`.
- M3-A raw transport corollary: exact raw repair transport under the atom-induced lever bijection.
- M3-B: `GroupSoundness + ResidualFaithfulness => GroupedRep_C(E) = ContractRep(C)`.
- M3-B two-realization corollary: grouped invariance through shared `ContractRep(C)`.
- M3-C: under `PsiDeletionMonotonicity`, `GroupedRep_C(E) = ContractRep(C) => GroupSoundness`.
- Equivalence corollary: for residually faithful realizations over `Psi`-deletion-monotone contracts, `GroupSoundness` iff grouped correctness.
- Candidate B instantiation: artifact-backed PASS for M3-B.

M3-C remains "promotion pending" until the Section 6 checklist is completed.

## 11. Evidence Inventory

Required evidence is limited to:

- M1.5 Candidate B raw non-canonicity evidence.
- M3 Candidate B `GroupSoundness` audit result.
- The 16-case residual faithfulness table.
- The `RawRep` singleton completeness proof.
- `PsiDeletionMonotonicity` over the 16-row lattice.
- Candidate B grouped family: `{ {asymm}, {un}, {minlib}, {no_cycle4} }`.
- The Arrow prerequisites scope wall.

No new evidence requirements are added by this allocation.

## 12. Writing Order

1. Section 2 definitions.
2. Section 3 M3-A.
3. Section 4 M3-B.
4. Section 5 M3-C.
5. Section 6 Candidate B audit.
6. Section 7 Related Work.
7. Section 8 Scope boundary / Arrow.
8. Section 9 Discussion.
9. Section 1 Introduction.
10. Abstract last.

Definitions and theorem statements should be stabilized before writing the Introduction. The Abstract must be written last to avoid overclaiming or underclaiming.

## 13. What Is Appendix-Only

The following material is appendix-only:

- full audit tables;
- detailed artifact paths;
- the schematic non-monotone counterexample, unless space permits a short main-text remark;
- Arrow prerequisite tables;
- long proof-skeleton details not needed in the main text;
- extended M2 transfer-contract background;
- raw JSON artifact excerpts;
- the atomicity dependency table.

The claim discipline table must not move to the appendix. It belongs in the main text or introduction-facing discussion.

## 14. Next Deliverables After This Document

After this allocation document, the next deliverables are:

1. Lean module design for M3-A/B/C; and
2. the `papers/m3/` TeX scaffold.

No further M3 planning documents should be created before one of those two deliverables exists.

## 15. Acceptance Criteria

- Create exactly one file: `docs/m3_paper_section_allocation.md`.
- Make no code changes.
- Run no solvers.
- Create no new experiments.
- Add no new theorem claims.
- Declare this document to be the final M3 meta/planning document.
- Target a standalone full paper under `papers/m3/`.
- Record the Lean formalization decision.
- Include the M3-C promotion checklist.
- Include Related Work in the manuscript map.
- Include all prohibited overclaims in the claim discipline table.
- Plan exactly three figures.
- Designate exactly two manuscript main-text tables: theorem comparison and claim discipline.
- Put the Abstract last in the writing order.
- Make Lean module design and the `papers/m3/` TeX scaffold the next deliverables, not another meta document.
