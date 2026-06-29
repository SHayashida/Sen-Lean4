# M4 Short Paper Outline

Status: short paper outline / docs-only
Depends on:

- M4 paper claim scaffold
- M4 finite-data closure
- M4 semantic encoding boundary
- M4 Level B right-atom Lean bridge

Current authorization: outline only
Not authorized:

- full paper manuscript
- Lean theorem
- Python/CNF correctness proof
- solver rerun
- checker rerun
- 3-voter run
- family-scale theorem
- warrant-contract implementation

## 1. Purpose

This outline translates the M4 paper claim scaffold into a short paper
structure.

The goal is to prepare a paper-facing outline without drafting the full
manuscript. The outline fixes where to introduce the methodology, the
finite-data certificate, the semantic boundary, the Level B Lean bridge, and
the Level C future-work boundary.

The outline preserves the maximum safe claim:
M4 is an auditable formal-methods methodology contribution for finite
social-choice artifacts, not a new general theorem of Sen.

## 2. Working Title Options

1. Auditable Repair Geometry for a Finite Social-Choice Impossibility Artifact
2. Claim Boundaries for Repair Reports in Finite Social Choice
3. A Machine-Audited Phase Diagram for Repair Reporting in Sen24
4. Auditable Abstraction Contracts for Finite Social-Choice Repairs
5. From Impossibility Certificates to Repair Reports: A Finite Audit Case
   Study
6. Repair Reportability Under Declared Encodings: A Sen24 Phase Diagram
7. Separating Certificates, Semantics, and Reports in Finite Social Choice

Preferred working title:

```text
Auditable Repair Geometry for a Finite Social-Choice Impossibility Artifact
```

Rationale:
This title emphasizes methodology and auditability, avoids claiming a general
Sen theorem, and keeps the finite-artifact boundary visible.

## 3. Target Paper Identity

Target identity:
short formal-methods / computational social choice methodology paper.

Not primarily:

- pure COMSOC theorem paper;
- full formal verification paper;
- empirical AI audit paper;
- general Sen theorem paper.

Primary audience:

- formal methods researchers interested in auditability and proof artifacts;
- computational social choice researchers interested in repair/reporting
  claims;
- software assurance researchers interested in evidence-vs-claim boundaries;
- doctoral supervisors evaluating a formal-methods methodology thesis.

## 4. Core Thesis

Core thesis:
When an impossibility artifact is encoded and repaired, the repair report is
only entitled to the claims supported by its declared encoding, finite
certificate, and semantic bridges. M4 demonstrates this discipline on a finite
Sen24 setting by producing a complete machine-audited phase diagram while
explicitly separating semantic assumptions and remaining artifact-correctness
obligations.

Shorter version:

```text
M4 shows how to make repair reporting auditable by separating finite certificates, semantic targets, and unproved artifact-correctness obligations.
```

## 5. Abstract Skeleton

Sentence 1: problem.

```text
Repair claims for formal impossibility artifacts can overstate what has actually been certified when encoding assumptions, grouping choices, and reporting layers are conflated.
```

Sentence 2: method.

```text
We study this problem in a declared selector-free semantic encoding of the two-voter, four-alternative Sen setting.
```

Sentence 3: finite-data result.

```text
The M4 certificate machine-audits the bundled-mask x obstruction-shape phase diagram, classifying all 48 cells and verifying SAT-cell RepairEmpty, UNSAT-cell orbit-fiber exactness, support truncation for shape-blind reports, and no mixedness within mask x shape cells.
```

Sentence 4: Lean bridge.

```text
A small Lean bridge backs the central right-atom semantic target by defining `RightAtomSemantics := x ≠ y ∧ Decisive F i x y`, proving orientation invariance, and showing that two fixed right atoms with distinct voters suffice for Lean `MINLIB`.
```

Sentence 5: boundary.

```text
We deliberately separate these internal certificate and semantic-target results from unproved Level C obligations, including Python/CNF artifact correctness and semantic-to-CNF correctness.
```

Compressed abstract outline draft, not final manuscript:

```text
Repair claims for formal impossibility artifacts can overstate what has actually been certified when encoding assumptions, grouping choices, and reporting layers are conflated. We study this problem in a declared selector-free semantic encoding of the two-voter, four-alternative Sen setting. The M4 certificate machine-audits the bundled-mask x obstruction-shape phase diagram, classifying all 48 cells and verifying SAT-cell RepairEmpty, UNSAT-cell orbit-fiber exactness, support truncation for shape-blind reports, and no mixedness within mask x shape cells. A small Lean bridge backs the central right-atom semantic target through decisiveness, orientation invariance, and a fixed sufficient direction into minimal liberalism. We separate these internal certificate and semantic-target results from unproved Level C obligations, including Python/CNF artifact correctness and semantic-to-CNF correctness.
```

## 6. Section-by-Section Outline

### Section 1: Introduction

Purpose:
Introduce repair-reporting overclaiming as the main problem. Explain why the
question is not whether Sen's theorem is true, but what a repair report is
entitled to say after encoding and auditing.

Must include:

- problem of claim drift;
- finite social-choice artifacts as audit objects;
- why repair reporting needs boundaries;
- preview of M4's answer.

Must not include:

- claim that M4 proves general Sen repair geometry;
- claim that semantic-to-CNF correctness is proved.

### Section 2: Background and Running Setting

Purpose:
Introduce Sen24, impossibility artifacts, repairs, reports, and the declared
selector-free semantic encoding.

Must include:

- `n=2`, `m=4` finite setting;
- bundled residual masks;
- fixed-witness right atoms;
- obstruction shapes `O2`/`O3`/`O4`;
- explanation that the encoding is declared and audited, not proved fully
  correct.

### Section 3: Methodology: Claim Boundaries and Reportability

Purpose:
Present the methodological stack: domain, declared encoding, finite
certificate, semantic boundary, Lean semantic bridge, future Level C
obligations.

Must include:

- contribution stack;
- allowed vs forbidden claims;
- two-bridges framing;
- why finite certificates need semantic boundaries.

### Section 4: Finite-Data Certificate

Purpose:
State the machine-audited phase diagram result.

Must include:

- 48 bundled-mask x obstruction-shape cells;
- SAT-cell RepairEmpty;
- UNSAT-cell orbit-fiber exactness;
- shape-blind support truncation;
- no mixedness within mask x shape cells;
- Certificate 2 as finite-data certificate.

Must state:

```text
This is a finite-data certificate statement, not a structural necessity theorem.
```

### Section 5: Level B Lean Bridge for the Central Right Atom

Purpose:
Explain what the small Lean bridge proves and what it does not prove.

Must include:

- `RightAtomSemantics F i x y := x ≠ y ∧ Decisive F i x y`;
- orientation invariance via `Decisive.symm`;
- fixed two-rights sufficient direction into `MINLIB`;
- Bridge A crossed;
- Bridge B still uncrossed.

### Section 6: Limitations and Assurance Boundary

Purpose:
Make limitations explicit before reviewer objection.

Must include:

- no Python `_right_clauses` correctness;
- no `FiniteSchema` correctness;
- no SAT assignment semantics;
- no semantic-to-CNF correctness;
- no full selector-free equivalence to `MINLIB`;
- no structural Mask-Shape theorem;
- no general Sen theorem.

### Section 7: Related Work / Positioning

Purpose:
Position the paper relative to formal methods, computational social choice,
proof artifacts, and software assurance.

Do not write citations yet unless already available in existing repo docs. Use
placeholders if needed.

Potential clusters:

- computational social choice and impossibility theorems;
- SAT/SMT-aided social choice;
- proof artifacts and certified computation;
- software assurance / assurance cases;
- explainability / auditability of formal artifacts.

### Section 8: Conclusion and Future Work

Purpose:
Restate M4 as methodology and list future work.

Must include future work buckets:

- Level C artifact bridge;
- structural explanation of Mask-Shape Collapse Law;
- generalization beyond Sen24;
- proof-carrying artifact release.

## 7. Contribution Bullets

Contributions:

1. A claim-boundary methodology for repair reporting in finite social-choice
   artifacts.
2. A complete finite-data certificate for the declared Sen24 bundled-mask x
   obstruction-shape phase diagram.
3. A Level B Lean semantic bridge for the central right atom, including
   orientation invariance and a fixed sufficient direction into `MINLIB`.
4. An explicit separation of crossed semantic bridges from remaining Level C
   artifact-correctness obligations.

Conservative contributions:

1. We document and audit a declared selector-free semantic encoding for Sen24
   repair reporting.
2. We certify the finite phase diagram induced by bundled masks and
   obstruction shapes.
3. We give a small Lean semantic target for the central right atom.
4. We make unproved semantic-to-CNF obligations explicit rather than hiding
   them in the certificate claim.

## 8. Main Claim Placement

Place the exact main claim at the end of the Introduction and repeat it at the
start of Section 4.

Recommended wording:
Under the declared selector-free semantic encoding of Sen24, the M4 artifacts
provide a complete finite-data certificate for the bundled-mask x
obstruction-shape phase diagram of inconsistency and repair reporting. The
central right-atom semantic target is Lean-backed, but Python/CNF artifact
correctness remains future work.

## 9. Certificate Statement Placement

Place the certificate statement in Section 4 before discussing implications.

Recommended wording:
For the declared Sen24 selector-free semantic encoding, Certificate 2 covers
the 48 bundled-mask x obstruction-shape cells. SAT cells are actively
classified as RepairEmpty, UNSAT cells satisfy orbit-fiber exactness,
shape-blind reporting obeys support truncation, and no mask x shape cell is
internally mixed.

Immediately after this statement, add:

```text
This is a finite-data certificate statement, not a structural necessity theorem.
```

## 10. Semantic Boundary Placement

Place the semantic boundary early, ideally in Section 1 or Section 2, before
the certificate result.

Recommended wording:
The finite-data certificate is internal to the declared selector-free semantic
encoding. It assumes the declared encoding as the audited object of study. It
does not by itself prove Python `_right_clauses` correctness,
semantic-to-CNF correctness, CNF artifact correctness, or full selector-free
encoding equivalence to `MINLIB`.

## 11. Level B Lean Bridge Placement

Place the Level B Lean bridge in Section 5, after the finite-data certificate.

Recommended wording:
The central right-atom semantic target is Lean-backed by
`RightAtomSemantics F i x y := x ≠ y ∧ Decisive F i x y`. The bridge proves
orientation invariance for unordered-pair use and a fixed sufficient direction
from two right atoms with distinct voters to Lean `MINLIB`. It does not prove
that Python `_right_clauses` or CNF artifacts correctly encode that target.

## 12. Two-Bridges Placement

Include a two-bridges box or table in Section 5 or Section 6.

Bridge A:
Semantic target <-> Lean social choice.
Status: crossed.

Bridge B:
Python/CNF artifact <-> Lean semantic target.
Status: not crossed / Level C future work.

| Bridge | Connects | Status | Paper claim |
| --- | --- | --- | --- |
| A | `RightAtomSemantics` <-> Lean `Decisive` / fixed `MINLIB` sufficiency | Crossed | Lean-backed semantic target |
| B | Python `_right_clauses` / CNF artifacts <-> `RightAtomSemantics` | Not crossed | Future Level C obligation |

## 13. Limitations Paragraph

Ready-to-use limitations paragraph:

```text
This paper does not claim end-to-end semantic correctness of the generated artifacts. In particular, we do not prove that Python `_right_clauses` correctly encode `RightAtomSemantics`, that `FiniteSchema` profile indices correspond to Lean profiles, that SAT assignments correspond to Lean SWFs, or that the generated CNF artifacts satisfy a semantic-to-CNF correctness theorem. The contribution is instead to separate these obligations from the finite-data certificate and to make the remaining trust boundary explicit.
```

## 14. Reviewer-Risk Integration

Risk 1: finite enumeration
Handle in Introduction and Methodology.
Emphasize auditable decomposition, not enumeration alone.

Risk 2: semantic-to-CNF gap
Handle in Semantic Boundary and Limitations.
Use two-bridges table.

Risk 3: overclaiming Sen
Handle in Introduction and Main Claim.
Avoid "Sen theorem repair geometry."

Risk 4: Lean bridge too weak
Handle in Section 5.
Say Lean-backed semantic target, not encoding correctness.

Risk 5: MINLIB lemma misread
Handle in Section 5.
Say sufficient direction only.

Risk 6: structure vs enumeration
Handle in Section 4 and Conclusion.
Say finite-data certificate, not structural necessity theorem.

## 15. Figures and Tables

Figure 1: Claim-boundary stack
Caption:
M4 separates domain assumptions, declared semantic encoding, finite-data
certificate, Lean semantic bridge, and remaining Level C artifact-correctness
obligations.

Figure 2: Mask x obstruction-shape phase diagram
Caption:
The 48-cell bundled-mask x obstruction-shape phase diagram classified by the
M4 finite-data certificate.

Figure 3: Two bridges
Caption:
Bridge A is crossed by the Level B Lean semantic bridge; Bridge B, from
Python/CNF artifacts to the Lean semantic target, remains future work.

Table 1: Allowed and forbidden claims
Caption:
Claim discipline for paper-facing M4 statements.

Table 2: Reviewer risks and mitigations
Caption:
Likely reviewer objections and the corresponding claim-boundary responses.

Table 3: Evidence sources
Caption:
Mapping from paper claims to repository artifacts.

## 16. Advisor / Laboratory Discussion Use

For Hasebe / MAS / formal methods:
Use the outline to present M4 as a finite formal analysis of multi-agent
social-decision artifacts. Emphasize repair geometry, obstruction shape,
formal methods methodology, and future structural explanation.

For Ishikawa / assurance / software engineering:
Use the outline to present M4 as an assurance-style case study. Emphasize
explicit claim boundaries, evidence-vs-claim discipline, Lean-backed semantic
target, and remaining Level C artifact-correctness obligations.

Question to ask both:
Is this acceptable as an auditable formal-methods methodology contribution,
with Level C future work, or should the dissertation require end-to-end
semantic-to-CNF correctness?

## 17. What Not To Write Yet

Do not write the full manuscript yet.
Do not add citations unless already available in repo notes.
Do not expand related work before advisor expectation is clarified.
Do not attempt Level C artifact correctness in this outline.
Do not claim structural necessity for Mask-Shape Collapse Law.
Do not write as if the paper proves a general Sen theorem.

## 18. Open Decisions Before Full Draft

Open decisions:

1. Target venue / audience: COMSOC, formal methods, software assurance, or
   interdisciplinary methodology.
2. Advisor expectation: methodology contribution vs end-to-end verification
   requirement.
3. Whether Level C remains future work or becomes a thesis requirement.
4. Whether structural explanation of Mask-Shape Collapse Law is needed before
   submission.
5. Whether the paper should be short-paper length or full-paper length.
6. Whether related work should emphasize social choice, formal methods, or
   software assurance.

## 19. Recommended Next Step

Recommended next step:
Use this outline in advisor/lab discussions before drafting the full
manuscript.

After advisor expectation is clarified, choose one path:

Path A: methodology paper
Move from this outline to a short manuscript draft.

Path B: end-to-end verification thesis
Pause paper drafting and scope Level C semantic-to-CNF feasibility.

Current recommendation:
Proceed with advisor discussion and then produce a short manuscript draft only
if Level C is accepted as future work.

## 20. Non-Claims

This outline does not claim:

- general Sen theorem;
- general social-choice theorem;
- structural Mask-Shape theorem;
- Python encoder correctness;
- Python `_right_clauses` correctness;
- `FiniteSchema` correctness;
- SAT assignment semantics;
- semantic-to-CNF correctness;
- CNF artifact correctness;
- full `MINLIB` equivalence;
- family-scale theorem;
- Arrow theorem;
- Gibbard-Satterthwaite theorem;
- that Level B bridge proves Level C correctness.

## 21. Next Authorized Action

The next authorized action is review of this short paper outline.

After review and advisor/lab discussion, the next writing action may be a
short manuscript draft only if Level C is accepted as future work. This
outline does not authorize full manuscript drafting, Lean work, Python/CNF
correctness proof, solver reruns, checker reruns, 3-voter work, family-scale
theorem work, or warrant-contract implementation.
