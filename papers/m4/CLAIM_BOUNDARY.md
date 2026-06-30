When a computer reports that no decision rule can meet every requirement we gave it, the practical question is larger than whether the run was performed correctly. We need to know which requirement is responsible, which change would repair the conflict, which parts of that answer are backed by the recorded evidence, and which parts depend on modeling choices outside the check. This paper studies that problem in a small but complete social-choice example: it enumerates the possible repairs, checks the recorded evidence, connects one central condition to a small formal proof, and separates those supported results from stronger correctness claims. It does not claim to solve social choice in general or to prove that every layer of the computer encoding is correct.

This document turns that motivation into explicit claim boundaries for the M4 preprint.

# M4 Claim Boundary

## 1. Plain-language motivation

The opening paragraph above is the required reader-facing entry point for the
preprint. The abstract and introduction should begin with the practical
question about what an impossibility artifact is entitled to report, then
introduce the technical vocabulary only after that question is clear.

## 2. Main preprint claim

Layer 1 is the paper's main intellectual contribution:

> A formal impossibility artifact should not only be checked for correctness;
> it should also be audited for what repair and reporting claims it is entitled
> to make. M4 develops this claim-boundary audit in the smallest Sen-style case,
> separating finite evidence, declared semantic assumptions, partial formal
> proof, and remaining correctness obligations.

Layer 2 is the technical instantiation:

> Under the declared M4 Sen24 encoding, M4 completes the finite
> repair-structure audit and provides a Lean-backed bridge for the central right
> condition, while leaving full artifact-level semantic-to-CNF correctness as
> future work.

The preprint should present Layer 1 as the main contribution. Layer 2 supplies
the concrete audited case and must not be broadened into an end-to-end
correctness claim.

## 3. Certified finite-data claims

The following claims are certified under the declared encoding and within the
declared Sen24 scope. They should be presented as finite-data audit results and
paper-facing certificate claims, not as structural theorems unless a separate
proof artifact is added.

- Bundled-mask x obstruction-shape organization: the certificate uses the 16
  minlib-active bundled masks and the three obstruction shapes `O2`, `O3`, and
  `O4` as the audited 48-cell organization.
- 48-cell finite audit: all cells are covered, with 18 `ALL_UNSAT` cells, 30
  `ALL_SAT` cells, no `MIXED_WITHIN_SHAPE` cells, and no `UNKNOWN` cells.
- SAT-cell repair classification: all 30 `ALL_SAT` cells are actively checked
  as `RepairEmpty` cells, with no repair objects created for those cells.
- UNSAT-cell orbit/fiber exactness: all 18 `ALL_UNSAT` cells are checked so
  that repair objects occur only in UNSAT cells, every cell-indexed grouped
  report fiber is exactly one complete repair orbit, and no partial orbit
  fragments remain.
- Support truncation for shape-blind reports: shape-blind reports are checked
  over UNSAT support, with the recorded 33 shape-blind fibers satisfying the
  support-truncation condition.
- No mixedness within mask x shape cells: the declared audit reports zero
  `MIXED_WITHIN_SHAPE` cells.

These claims are supported by the M4 finite-data closure note, the Certificate
2 phase-diagram checker result, and the mask-shape audit documents. They remain
claims about the declared finite object of study.

## 4. Lean-backed semantic claims

M4 may document the Level B bridge implemented in
`SocialChoiceAtlas/Sen/RightAtomBridge.lean`.

The Lean-backed semantic target is:

```lean
RightAtomSemantics F i x y := x ≠ y ∧ Decisive F i x y
```

The implemented Level B claims are:

- `RightAtomSemantics` packages endpoint distinctness with Lean `Decisive`.
- Orientation invariance for the unordered-pair use is backed by
  `rightAtomSemantics_symm` and `rightAtomSemantics_iff_swap`, using the
  relevant `Decisive.symm` result.
- Two fixed right conditions with distinct voters imply Lean `MINLIB` in the
  sufficient direction, through `twoRightAtoms_imply_MINLIB`.

M4 must not describe this as a full equivalence to `MINLIB`. The implemented
bridge is semantic-only and does not prove Python clause correctness, CNF
correctness, or artifact-level semantic-to-CNF correctness.

## 5. Declared semantic boundary

M4's finite-data claims are internal to the declared Sen24 encoding. The paper
may study that encoding as the audited object, but it must state that this is a
declared semantic boundary rather than a proved end-to-end correspondence
between every generated artifact and the Lean social-choice semantics.

The finite audit supports claims about the declared bundled masks, fixed right
conditions, obstruction shapes, cells, repair objects, and grouped reports. The
Level B Lean bridge backs the central right-condition target. The bridge from
Python/CNF artifacts to the Lean semantic target remains Level C future work.

## 6. Not claimed by M4

M4 does not claim:

- Python encoder correctness;
- `_right_clauses` correctness;
- `FiniteSchema` profile correctness;
- SAT assignment semantics as Lean social welfare functions;
- full semantic-to-CNF correctness;
- CNF artifact correctness;
- full selector-free encoding equivalence to Lean `MINLIB`;
- structural proof of the Mask-Shape Collapse Law, unless a separate structural
  proof artifact is later added;
- the general Sen theorem as a new M4 result;
- family-scale CNF/LRAT/atlas/repair lift.

The general Sen theorem belongs to the M2 semantic bridge and is not a new M4
claim.

## 7. Future correctness obligations

Level C is future assurance work. These obligations should be framed as the
next layer of assurance, not as hidden defects in the present preprint scope:

- a representation map between Lean profiles and finite schema profiles;
- a mapping between Lean strict preference predicates and generator variables;
- SAT assignment semantics as social welfare functions;
- a proof that Python right clauses encode the Lean right-condition semantics;
- artifact-level correctness for generated CNF.

Completing Level C would strengthen the project from a claim-boundary audit
over a declared encoding into an artifact-level semantic correctness result.
That stronger result is not required for the M4 preprint as scoped here.

## 8. Two-bridge status table

| Bridge | Status | M4 wording |
|---|---|---|
| Right-condition semantic target <-> Lean semantic predicate | crossed at Level B for the declared predicate definition | Lean-backed semantic target |
| Two fixed right conditions => Lean `MINLIB` | crossed in the sufficient direction by `twoRightAtoms_imply_MINLIB` | sufficient Lean bridge |
| Python right clauses <-> Lean right-condition semantics | not crossed | future Level C obligation |
| CNF artifacts <-> Lean semantics | not crossed | future Level C obligation |
| Full selector-free encoding equivalence | not crossed | not claimed |

## 9. Relationship to M1-M4

- M1 separates proof, audit, witness, and assumptions in the finite Sen24
  evidence layer.
- M1.5 shows that valid impossibility evidence does not determine a canonical
  raw repair report.
- M2 establishes the semantic obstruction bridge and the general Sen theorem;
  this is not an M4 claim.
- M3 gives conditions under which grouped repair reporting is justified.
- M4 closes the finite artifact line for the declared Sen24 encoding by making
  claim boundaries explicit: finite evidence, declared assumptions,
  Lean-backed semantic target, and future correctness obligations are reported
  separately.

## 10. Safe wording for the abstract and introduction

Good opening:

> Formal artifacts can certify that a decision rule is impossible,
> inconsistent, or repairable. But they do not automatically determine which
> repair or reporting claim is licensed by the evidence.

Avoid opening with:

> Under a declared selector-free semantic encoding, we audit the bundled-mask x
> obstruction-shape phase diagram...

The abstract and introduction should follow this order:

```text
question
-> why it matters
-> smallest case
-> method
-> technical vocabulary
-> claim boundary
```
