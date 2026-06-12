# M1.5 to M3 Transition: From Abstraction-Contract Gap to Lean-Backed Reportability

## 1. One-sentence spine

M1 builds an auditable finite atlas; M1.5 shows that even a trusted and clause-equivalent witness does not determine canonical raw repair explanations; M3 theoremizes the repair-reporting component of the abstraction-contract thesis as a reportability contract.

## 2. Corrected three-layer interpretation

The simple reading that M1 occupies only Layer 1 is too narrow. The dissertation spine is better understood through three related layers.

### Layer 1: Evidence / truth boundary

M1 primarily establishes the evidence contract: Proof / Audit / Witness / Assumption. Its central achievement is an auditable finite impossibility atlas whose claims can be traced to explicit specifications, generated artifacts, independent checks, and proof infrastructure.

### Layer 2: Raw repair geometry

M1 already crosses into repair geometry by recording the atlas frontier, MUS/MCS structure, and repair triangulation. M1.5 then isolates a sharper result: raw implementation-level repair explanations need not be canonical even when the compared witnesses remain trusted and clause-multiset equivalent.

### Layer 3: Reportability

M3 asks when implementation-level raw repairs may be grouped and reported as canonical contract-level repairs. It supplies explicit conditions for this passage rather than treating implementation lever names as an automatically valid reporting vocabulary.

M1 crosses into Layer 2 as an atlas and repair-geometry artifact, but it does not yet theoremize repair reportability.

## 3. Abstraction contract thesis and why M3 does not formalize all of it at once

M1.5 introduces the abstraction-contract thesis. The thesis says that finite witness validity does not by itself determine the abstraction level at which repairs should be compared or reported. A correct certificate may establish the status of a finite residual while leaving open which implementation distinctions should survive into an explanation.

The full abstraction-contract thesis is broader than M3. It includes evidence legitimacy, semantic interpretation, implementation representation, repair reporting, and future obligations that connect finite results to larger families. Those components need not share one formal interface or one proof method.

M3 therefore does not attempt to formalize the entire thesis. It formalizes the repair-reporting component because that is exactly the component exposed by the M1.5 raw non-canonicity witness. The Lean core abstracts away from CNF, SAT solving, proof logs, and the Candidate B artifact audit; it reasons over finite atom and lever sets with abstract retained-residual predicates.

M3 is not a retreat from the abstraction-contract thesis; it is the first theoremization of one of its components.

## 4. Two operational contracts in M1–M3

### Evidence contract

M1's evidence contract specifies what is proved, audited, witnessed, and left assumed. It governs the truth boundary of the finite atlas and prevents an artifact, solver result, or proof-layer statement from being used beyond its recorded support.

### Reportability contract

M3's reportability contract specifies when raw implementation repairs may be soundly reported as grouped repairs over declared contract atoms. Its core objects separate implementation levers, contract atoms, retained-residual feasibility, the grouping map, and inclusion-minimal repair predicates.

In M1–M3, the abstraction-contract thesis is operationalized through two contracts: the evidence contract and the reportability contract. Future work may add semantic, Lean-level, and finite-to-general bridge contracts.

These two contracts operationalize the parts used so far; they do not exhaust or redefine the broader abstraction-contract thesis.

## 5. M1.5 gap

Candidate B exposes the raw repair gap through two clause-equivalent representations of the same finite witness:

- the bundled representation has one implementation lever, `minlib`;
- the split representation replaces it with `decisive_voter0` and `decisive_voter1`;
- the bundled raw repair `{minlib}` transports to the two-lever set `{decisive_voter0, decisive_voter1}`;
- the split representation also has the finer singleton raw repairs `{decisive_voter0}` and `{decisive_voter1}`;
- therefore the bundled, transported, and split raw repair families do not coincide.

The mismatch arises because raw repairs are inclusion-minimal deletions over implementation levers. Refining one bundled lever into independently removable components changes that implementation-level deletion geometry even when the encoded clause multiset remains controlled.

This does not invalidate the witness. It shows that witness validity and raw repair reportability are different obligations.

Raw non-canonicity is not erased by M3.

## 6. M3 Lean core

The new modules under `SocialChoiceAtlas/Reportability/` implement the reportability theory at a pure finite-set level. `SatPsi` and `SatPhi` are abstract feasibility predicates over retained atom and lever sets. `RawRepair`, `ContractRepair`, and `GroupedRepair` use explicit inclusion-minimality, while `groupTouchAny` supplies the contract-level reporting map.

The paper roles correspond to Lean declarations as follows:

| Paper role | Lean declaration |
| --- | --- |
| M3-A atomic sufficient condition | `m3a_grouped_correctness` |
| M3-A raw transport | `m3a_raw_transport` |
| M3-B non-atomic sufficient condition | `m3b_grouped_correctness` |
| M3-B two-realization corollary | `m3b_two_realization` |
| M3-C monotone converse | `m3c_converse` |
| M3-B/C exactness under monotone contracts | `groupSoundness_iff` |
| audit-cost collapse | `audit_cost_collapse` |
| hierarchy: atomicity implies soundness | `atomicity_implies_groupSoundness` |

### M3-A: atomic interface

M3-A uses `RepairAtomicity` and residual faithfulness. Atomicity prevents partial-block deletion syntactically: every active atom has one lever, so arbitrary implementation deletions remain atom-aligned. `m3a_grouped_correctness` proves pointwise agreement between grouped and contract repairs, and `m3a_raw_transport` proves atom-indexed raw repair transport between two atomic realizations of the same contract.

### M3-B: non-atomic group soundness

M3-B permits multi-lever blocks. Instead of forbidding partial-block deletion, it requires `GroupSoundness`: every feasible implementation deletion must remain feasible after touch-any grouping at the contract level. With residual faithfulness, `m3b_grouped_correctness` proves pointwise grouped correctness, and `m3b_two_realization` obtains grouped invariance through the shared contract repair predicate. It does not claim raw repair transport.

### M3-C: monotone exactness

M3-C proves the converse under `PsiDeletionMonotonicity`. If grouped correctness already holds, `m3c_converse` derives `GroupSoundness` without assuming residual faithfulness. The theorem `groupSoundness_iff` combines this converse with M3-B: for residually faithful realizations over deletion-monotone reference contracts, report soundness exactly characterizes grouped repair correctness.

The hierarchy theorem `atomicity_implies_groupSoundness` shows that atomicity is a syntactic sufficient condition for report soundness, not the conceptual core. The kernel-checked examples reinforce both boundaries: group soundness can hold without atomicity, and grouped correctness can hold without group soundness when reference deletion monotonicity fails.

## 7. Fully active UNSAT note

The Lean core is stated for the general minimal-deletion predicate and may include the degenerate case where the fully active residual is already SAT. In the M3 impossibility-repair application, fully active UNSAT is a separate application-side assumption ensuring that the repair family has the intended interpretation.

This separation is deliberate. The transport and reportability proofs do not mathematically require top-level UNSAT, while an impossibility-repair narrative normally does. The application must therefore record fully active UNSAT without adding it as an unnecessary hypothesis to the abstract Lean theorems.

## 8. Candidate B as M3-B instantiation

Candidate B is non-atomic under the bundled reportability contract because:

```text
beta(minlib) = {decisive_voter0, decisive_voter1}.
```

Therefore M3-A is not the right theorem for Candidate B. Candidate B instantiates M3-B, not M3-A.

The artifact audit treats the bundled residual lattice as the reference contract and checks residual faithfulness against the split realization. It establishes that the five split singleton raw repairs group to contract deletions whose bundled residuals are SAT. Under reference deletion monotonicity, `audit_cost_collapse` captures the abstract argument that these complete raw-repair checks suffice for unrestricted `GroupSoundness`.

The resulting grouped family is:

```text
{asymm}, {un}, {minlib}, {no_cycle4}
```

The same witness is raw-noncanonical and grouped-canonical: raw repairs differ across bundled and split realizations, but the grouped reports coincide under the artifact-defined reportability contract.

This conclusion combines two different forms of support. The Lean modules prove the general M3-B and audit-collapse implications; the existing Candidate B artifacts discharge their finite application-side premises. The Lean examples are boundary witnesses for the abstract theory, not a formalization of Candidate B.

## 9. Scope discipline

- M3 does not prove that raw repairs are canonical.
- M3 does not erase or weaken M1.5.
- M3 does not claim semantic validity beyond the chosen contract.
- Candidate B uses an artifact-defined reportability contract. It must not be silently identified with a full semantic or Lean-level social-choice contract.
- Sen24 `minlib` is a fixed finite local-decisiveness lever, not a complete theory of liberal rights.
- The Sen24 setting fixes two voters, four alternatives, strict linear orders, a fixed rights assignment, and local no-cycle rationality artifacts.
- The `no_cycle3` and `no_cycle4` artifacts must retain their declared local-rationality interpretation rather than being silently generalized.
- Generalization to Arrow, Borda-style repairs, or broader theorem families requires a new atlas and may require a finite-to-general bridge theorem.

The reportability contract answers how repairs may be grouped once its reference residuals are accepted. It does not independently establish that those residuals have the intended full semantic meaning or that a finite result transfers to another theorem family.

## 10. Final dissertation-spine paragraph

M1 makes finite impossibility evidence auditable. M1.5 shows that auditable evidence does not determine raw repair presentation. M3 proves when repair presentation can nevertheless be earned at the grouped contract level. This is the transition from an auditable atlas to a reportability theory.
