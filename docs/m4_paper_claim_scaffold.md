# M4 Paper Claim Scaffold

Status: paper-facing claim scaffold / docs-only
Depends on:

- M4 finite-data closure
- M4 semantic encoding boundary
- M4 Level B right-atom Lean bridge

Current authorization: claim scaffold only
Not authorized:

- paper manuscript edit
- Lean theorem
- Python/CNF correctness proof
- solver rerun
- checker rerun
- 3-voter run
- family-scale theorem
- warrant-contract implementation

## 1. Purpose

This scaffold fixes how M4 should be presented in paper-facing and
doctoral-facing prose.

The goal is to prevent claim drift:
M4 is not a new general theorem of Sen.
M4 is an auditable formal-methods methodology contribution for finite
social-choice artifacts.

The scaffold must preserve the distinction between:

- internal finite-data certification under a declared encoding;
- Lean-backed semantic target for the central right atom;
- unproved semantic-to-CNF correctness.

## 2. Positioning Decision

Decision:
M4 should be framed as an auditable methodology for social-choice artifacts.

The paper should not be framed as:

- a new theorem of Sen;
- a general theorem of social choice;
- an end-to-end Lean verification of Python/CNF artifacts;
- a structural proof of the Mask-Shape Collapse Law.

The paper should be framed as:

- a finite, machine-audited phase diagram for repair geometry under a
  declared selector-free semantic encoding;
- a demonstration of how impossibility, repair, abstraction, and reportability
  claims can be separated into auditable layers;
- a methodology for making claim boundaries explicit in formal social-choice
  artifacts.

## 3. One-Sentence Contribution

Preferred version:

```text
M4 turns a finite social-choice impossibility setting into a machine-audited phase diagram of inconsistency and repair geometry, with explicit semantic boundaries and a Lean-backed target for its central right atom.
```

Stricter version:

```text
Under a declared selector-free semantic encoding of Sen24, M4 machine-verifies the bundled-mask x obstruction-shape phase diagram and separates internal certificate claims from remaining encoding-correctness obligations.
```

Lab-facing version:

```text
M4 is an assurance-style case study for formal social-choice artifacts: it separates finite-data certificates, semantic assumptions, Lean-backed semantic targets, and future artifact-correctness obligations.
```

## 4. Main Contribution Stack

Layer 0: Social-choice problem domain
Sen24 finite setting: `n=2`, `m=4`.

Layer 1: Declared selector-free semantic encoding
Defines bundled residual masks, fixed-witness right atoms, and obstruction
shapes.

Layer 2: Finite-data certificate
Machine-audited 48-cell phase diagram:

- SAT-cell RepairEmpty;
- UNSAT-cell orbit-fiber exactness;
- shape-blind support truncation;
- no mixedness within mask x shape cells.

Layer 3: Semantic boundary
Encoding correctness / Sen-faithfulness is explicitly separated from internal
finite-data certification.

Layer 4: Level B Lean semantic bridge
`RightAtomSemantics := x ≠ y ∧ Decisive F i x y`;
orientation invariance via `Decisive.symm`;
fixed two-rights package implies Lean `MINLIB`.

Layer 5: Remaining Level C obligation
Python/CNF artifact correctness remains future work.

Evidence sources:

- `docs/m4_finite_data_closure_note.md`: finite-data closure and counts;
- `docs/m4_certificate2_phase_diagram_checker_result.md`: Certificate 2
  checker verdict;
- `docs/m4_scope_decision_mask_shape_phase_diagram.md`: mask-shape scope and
  non-circularity;
- `docs/m4_semantic_encoding_boundary.md`: declared encoding boundary;
- `docs/m4_right_atom_decisive_bridge_lean_result.md`: implemented Level B
  Lean bridge;
- `SocialChoiceAtlas/Sen/RightAtomBridge.lean`: semantic wrapper,
  orientation lemmas, and fixed two-rights sufficient direction.

## 5. Exact Main Claim

Main claim:
Under the declared selector-free semantic encoding of Sen24, the M4 artifacts
provide a complete finite-data certificate for the bundled-mask x
obstruction-shape phase diagram of inconsistency and repair reporting. The
central right-atom semantic target is Lean-backed, but Python/CNF artifact
correctness remains future work.

This is the maximum safe claim.
Do not strengthen it into a general Sen theorem or semantic-to-CNF correctness
theorem.

## 6. Certificate Statement

Certificate statement:
For the declared Sen24 selector-free semantic encoding, Certificate 2 covers
the 48 bundled-mask x obstruction-shape cells. SAT cells are actively
classified as RepairEmpty, UNSAT cells satisfy orbit-fiber exactness,
shape-blind reporting obeys support truncation, and no mask x shape cell is
internally mixed.

This is a finite-data certificate statement, not a structural necessity
theorem.

## 7. Encoding Boundary Statement

Encoding boundary:
The finite-data certificate is internal to the declared selector-free semantic
encoding. It assumes the declared encoding as the audited object of study.

It does not by itself prove:

- Python `_right_clauses` correctness;
- semantic-to-CNF correctness;
- CNF artifact correctness;
- full selector-free encoding equivalence to `MINLIB`.

The paper should front-load this boundary before stating strong certificate
results.

## 8. Level B Lean Bridge Statement

Level B bridge:
The central M4 right-atom semantic target is Lean-backed.

Implemented:

- `RightAtomSemantics F i x y := x ≠ y ∧ Decisive F i x y`;
- orientation invariance for unordered-pair use;
- fixed two-rights package sufficient for Lean `MINLIB`.

This bridge connects the intended semantic target of the right atom to
existing Lean social-choice notions.
It does not prove that Python `_right_clauses` or CNF artifacts correctly
encode that target.

## 9. Two Bridges: Crossed and Uncrossed

Bridge A: semantic target to Lean social choice
Status: crossed.

M4 right-atom semantic target:

```text
RightAtomSemantics F i x y := x ≠ y ∧ Decisive F i x y
```

Lean-backed facts:

- endpoint distinctness aligns with canonical-pair discipline;
- orientation invariance follows from `Decisive.symm`;
- two fixed right atoms with distinct voters imply Lean `MINLIB`.

Bridge B: Python/CNF artifact to Lean semantic target
Status: not crossed.

Still unproved:

- `_right_clauses` generates exactly the constraints represented by
  `RightAtomSemantics`;
- `FiniteSchema.profiles` corresponds to Lean profiles;
- `schema.var_p` corresponds to Lean social strict preference;
- SAT assignments correspond to Lean SWFs;
- generated CNF artifacts satisfy a semantic-to-CNF correctness theorem.

The paper may say Bridge A is implemented.
The paper must say Bridge B remains future work.

## 10. What the Paper May Claim

Allowed claims:

- M4 provides a complete finite-data certificate under a declared
  selector-free semantic encoding.
- The 48-cell bundled-mask x obstruction-shape phase diagram is
  machine-audited.
- Shape resolves the residual mixedness left by mask-only analysis.
- The central right-atom semantic target is Lean-backed.
- The unordered-pair convention for right atoms is supported by a Lean
  orientation lemma.
- A fixed two-rights package is sufficient for Lean `MINLIB`.
- Remaining artifact-correctness obligations are explicit.

## 11. What the Paper Must Not Claim

Forbidden claims:

- M4 proves a general theorem of Sen.
- M4 proves a general theorem of social choice.
- M4 proves semantic-to-CNF correctness.
- M4 proves Python `_right_clauses` correctness.
- M4 proves CNF artifact correctness.
- M4 proves full selector-free encoding equivalence to `MINLIB`.
- M4 proves the Mask-Shape Collapse Law structurally.
- M4 proves a family-scale theorem.
- The finite-data certificate alone proves Sen-faithfulness.
- Level B bridge proves encoding correctness.

## 12. Theorem / Certificate Statement Drafts

### Statement S0: safest

```text
Under the declared selector-free semantic encoding, the M4 certificate exhaustively classifies all Sen24 bundled-mask x obstruction-shape cells and verifies the reported finite-data properties of each cell.
```

### Statement S1: preferred paper statement

```text
Under the declared selector-free semantic encoding of Sen24, M4 machine-verifies a complete bundled-mask x obstruction-shape phase diagram for inconsistency and repair reporting. The central right-atom semantic target is Lean-backed, while semantic-to-CNF correctness remains a separate future obligation.
```

### Statement S2: too strong / reject

```text
M4 proves the repair geometry of Sen's theorem.
```

S2 is forbidden.

## 13. Abstract Claim Language

Abstract-safe language:

```text
We study how repair claims for finite social-choice impossibility artifacts can be made auditable without collapsing semantic assumptions into certificate results. For a declared selector-free semantic encoding of the two-voter, four-alternative Sen setting, we machine-audit the bundled-mask x obstruction-shape phase diagram and show that obstruction shape resolves all residual mixedness left by mask-only classification. The resulting certificate verifies SAT-cell emptiness, UNSAT-cell orbit-fiber exactness, and support truncation for shape-blind reports. A small Lean bridge backs the semantic target of the central right atom by connecting it to decisiveness and a fixed sufficient direction for minimal liberalism. We deliberately separate these internal certificate results from unproved semantic-to-CNF correctness obligations.
```

Shorter version:

```text
This paper contributes an auditable methodology, not a new general Sen theorem: it separates finite-data certification, semantic boundaries, Lean-backed semantic targets, and remaining artifact-correctness obligations.
```

## 14. Introduction Claim Language

Introduction-safe language:

```text
The central problem is not whether Sen's theorem is true. The problem is what a repair report is entitled to say after an impossibility artifact is encoded, grouped, and audited. M4 treats this as a claim-boundary problem. It asks which repair reports are internally certified by a declared finite encoding, which semantic assumptions are being relied on, and which correctness obligations remain outside the certificate.
```

This framing should appear before any strong phase-diagram result.

## 15. Reviewer Risk Table

| Risk | Likely reviewer question | Correct answer | Mitigation in paper |
| --- | --- | --- | --- |
| finite enumeration | Is this just a finite enumeration of Sen24? | It is finite, but the contribution is the auditable decomposition of repair reporting into mask, obstruction shape, orbit fibers, report fibers, and explicit claim boundaries. | Front-load methodology and claim-boundary contribution; present Sen24 as the first complete finite audit case. |
| semantic-to-CNF gap | Do you prove that Python `_right_clauses` correctly encode Lean `RightAtomSemantics`? | No. Level B proves the Lean semantic target; Level C semantic-to-CNF correctness remains future work. | Include the two-bridges table and non-claims paragraph. |
| overclaiming Sen | Do you prove a new theorem of Sen or social choice? | No. M4 provides a finite-data certificate under a declared encoding and a methodology for auditable repair reporting. | Avoid "Sen theorem repair geometry" language. |
| Lean bridge too weak | Does the Lean bridge prove the certificate is semantically correct? | No. It backs the central right-atom semantic target but does not prove Python/CNF artifact correctness. | Say "Lean-backed semantic target," not "Lean-proved encoding correctness." |
| optional MINLIB lemma misread | Does `twoRightAtoms_imply_MINLIB` prove full equivalence to `MINLIB`? | No. It proves only a sufficient direction for fixed witnesses. | State no necessity direction and no full selector-free equivalence. |
| structure vs enumeration | Do you prove the Mask-Shape Collapse Law structurally? | No. The collapse is finite-audit-supported in the declared Sen24 encoding; structural necessity remains future work. | Use "certificate-supported phase diagram," not "structural theorem," unless later proved. |

## 16. Advisor / Laboratory Positioning

### For Hasebe / MAS / formal methods / multi-agent systems

Position M4 as a finite formal analysis of multi-agent social-decision
artifacts:

- repair reporting as a property of encoded multi-agent impossibility
  artifacts;
- obstruction shape as a structural coordinate for residual inconsistency;
- Lean bridge as semantic grounding for the central right atom;
- future work toward structural explanation and broader multi-agent families.

Emphasize:

- formal-methods methodology;
- MAS/social-choice connection;
- repair geometry and obstruction classification.

Do not pitch primarily as:

- full end-to-end verified encoder;
- pure software assurance case;
- general Sen theorem.

### For Ishikawa / software engineering / assurance / trustworthy systems

Position M4 as an assurance-style case study for formal social-choice
artifacts:

- explicit claim boundary;
- finite-data certificate;
- semantic assumption separation;
- Lean-backed semantic target;
- residual Level C artifact-correctness obligation.

Emphasize:

- assurance case;
- trust boundary;
- evidence vs claim discipline;
- what the artifact proves and what it does not prove.

Do not pitch primarily as:

- purely mathematical Sen theorem;
- complete end-to-end verification;
- unchecked enumeration.

## 17. Figure and Table Plan

Figure 1: Claim-boundary stack
Sen24 domain -> declared semantic encoding -> finite-data certificate -> Lean
semantic bridge -> remaining Level C obligations.

Figure 2: Mask x obstruction-shape phase diagram
48 cells, SAT/UNSAT/RepairEmpty/orbit-fiber status.

Figure 3: Two bridges
Bridge A crossed: `RightAtomSemantics` <-> `Decisive`.
Bridge B uncrossed: Python/CNF <-> `RightAtomSemantics`.

Table 1: Allowed vs forbidden claims.

Table 2: Reviewer risk table.

Table 3: Contribution stack and evidence sources.

## 18. Future Work Boundary

Future work should be explicitly separated into:

Level C artifact bridge:

- Python `_right_clauses` correctness;
- `FiniteSchema` profile correctness;
- SAT assignment semantics;
- semantic-to-CNF correctness.

Structural theory:

- structural explanation of the Mask-Shape Collapse Law;
- generalization beyond Sen24;
- family-scale transfer;
- Arrow / Gibbard-Satterthwaite transfer.

Assurance packaging:

- proof-carrying artifact release;
- immutable result manifests;
- reproducibility package.

## 19. Decision Gate: Is Level C Required?

Decision gate for doctoral supervision:

If the dissertation is accepted as an auditable formal-methods methodology
contribution:
Level C may remain future work, provided the paper front-loads the two-bridges
distinction and non-claims.

If the dissertation is required to be an end-to-end verification thesis:
Level C becomes mandatory before final defense.

Current recommendation:
proceed with paper scaffold and advisor discussion before attempting Level C.

## 20. Recommended Next Writing Step

Recommended next writing step:
produce a short M4 paper outline from this scaffold.

The outline should contain:

- abstract skeleton;
- introduction skeleton;
- contribution bullets;
- theorem/certificate statement;
- limitation paragraph;
- reviewer-risk table.

Do not yet write the full paper until advisor expectation is clarified.

## 21. Non-Claims

This scaffold does not claim:

- general Sen theorem;
- structural Mask-Shape theorem;
- semantic-to-CNF correctness;
- Python encoder correctness;
- CNF artifact correctness;
- full `MINLIB` equivalence;
- family-scale theorem;
- Arrow theorem;
- Gibbard-Satterthwaite theorem;
- that Level B bridge proves Level C correctness.

## 22. Next Authorized Action

The next authorized action is review of this paper claim scaffold.

After review, the recommended next writing task is a short M4 paper outline
that uses this scaffold as its claim boundary. This document does not
authorize paper manuscript edits, Lean work, Python/CNF correctness proof,
solver reruns, checker reruns, 3-voter work, family-scale theorem work, or
warrant-contract implementation.

## Short Paper Outline Follow-up

A short paper outline has been added to translate this claim scaffold into a
paper-facing structure.

See `docs/m4_short_paper_outline.md`.
