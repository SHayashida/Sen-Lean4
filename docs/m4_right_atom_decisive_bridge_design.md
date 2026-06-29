# M4 Level B Design: `right_atom` and Lean `Decisive`

Status: Level B bridge design / docs-only
Depends on: M4 right-atom bridge feasibility note
Current authorization: design note only
Not authorized: Lean implementation, encoding-correctness theorem, solver rerun, checker rerun, 3-voter run, warrant-contract implementation, paper-claim promotion

## 1. Purpose

This document designs the minimal Level B Lean bridge for the M4 right-atom
semantics.

The task is not to prove artifact correctness.
The task is to specify a small Lean-level semantic bridge that connects the M4
right-atom name to the existing Lean `Decisive` concept and supports the
unordered-pair convention used by M4.

This design follows the feasibility verdict:
Level B is feasible as a Lean semantic predicate bridge.
Level C full artifact correctness is not yet ready.

## 2. Design Decision

Decision:
The next Lean implementation, if authorized later, should target Level B only.

The minimal useful bridge should not be a bare definitional alias alone.
It should include a right-atom semantic wrapper with explicit
distinct-endpoint discipline and an orientation lemma using `Decisive.symm`.

This gives M4 a Lean-backed semantic target for `right(voter,{x,y})` without
claiming Python clause correctness or semantic-to-CNF correctness.

## 3. Source Constraints

Lean-side constraints:

- `Decisive F i x y` is already defined in
  `SocialChoiceAtlas/Axioms/Liberalism.lean`.
- `MINLIB F` is already defined in
  `SocialChoiceAtlas/Axioms/Liberalism.lean`.
- `Decisive.symm` is already proved.
- `MINLIB` includes distinct endpoints for both decisive pairs.
- `Decisive` itself does not appear to require `x ≠ y`.
- `SocialChoiceAtlas/Core/Profile.lean` defines `Profile` as a voter-indexed
  ranking assignment and `SWF` as a function from profiles to social binary
  relations.
- `SocialChoiceAtlas/Core/Profile.lean` defines `prefers_i p i x y` through
  the voter's ranking in profile `p`.
- `SocialChoiceAtlas/Core/Basics.lean` defines `strictPart R x y` as
  `R x y ∧ ¬ R y x`.

M4 script-side constraints:

- `right_atom(voter,pair)` uses `canonical_pair`.
- `canonical_pair` rejects equal endpoints.
- M4 right atoms represent unordered alternative pairs.
- `_right_clauses` emits one social-pairwise clause per finite profile.
- The current bridge design does not prove `_right_clauses` correctness.
- `encoding/schema.py` enumerates finite profiles through
  `FiniteSchema.profiles`, records `n_profiles`, and defines `var_p`,
  `prefers`, `pref0`, and `pref1`.

## 4. Target Lean File

Proposed future Lean file:

```text
SocialChoiceAtlas/Sen/RightAtomBridge.lean
```

The future Lean file should be small and semantic-only.
It should import only what is necessary, likely
`SocialChoiceAtlas.Axioms.Liberalism`.
It should not import SAT, CNF, scripts, certificates, or M4 checker artifacts.

The file name is provisional.
This design note authorizes no Lean file creation.

## 5. Import Boundary

Recommended import boundary:

- `SocialChoiceAtlas.Axioms.Liberalism`

Avoid:

- SAT/CNF modules;
- generated certificate modules;
- Python artifact references;
- M4 checker outputs;
- any family-scale or 3-voter machinery.

## 6. Proposed Semantic Wrapper

Recommended Lean predicate shape:

```lean
def RightAtomSemantics (F : SWF Voter Alt) (i : Voter) (x y : Alt) : Prop :=
  x ≠ y ∧ Decisive F i x y
```

Rationale:

- M4 `right_atom` only exists for distinct endpoints.
- Lean `Decisive` itself can be stated for any ordered pair.
- Adding `x ≠ y` aligns the Lean wrapper with M4's `canonical_pair`
  discipline.

Alternative:
If implementation pressure favors minimalism, `RightAtomSemantics` may
initially be an abbreviation for `Decisive F i x y`, but then the bridge is
mostly naming. The design-preferred version includes `x ≠ y`.

## 7. Distinct-Endpoint Discipline

The bridge should preserve the M4 endpoint discipline.

M4 script:
`canonical_pair(a,b)` rejects `a = b`.

Lean design:
`RightAtomSemantics F i x y` should include or require `x ≠ y`.

This prevents the bridge from accidentally giving meaning to script-level
right atoms that M4 never generates.

## 8. Orientation Lemma

Core theorem target:

```lean
theorem rightAtomSemantics_symm
    {F : SWF Voter Alt} {i : Voter} {x y : Alt}
    (h : RightAtomSemantics F i x y) :
    RightAtomSemantics F i y x := ...
```

or equivalently:

```lean
theorem rightAtomSemantics_iff_swap
    {F : SWF Voter Alt} {i : Voter} {x y : Alt} :
    RightAtomSemantics F i x y ↔ RightAtomSemantics F i y x := ...
```

Expected proof ingredients:

- `Ne.symm` or equivalent endpoint inequality symmetry;
- `Decisive.symm`.

This theorem is the main non-vacuous Level B contribution.
It supports treating M4 right atoms as unordered-pair rights at the semantic
Lean level.

## 9. Optional Fixed-Two-Rights MINLIB Lemma

Optional theorem target:

```lean
theorem twoRightAtoms_imply_MINLIB
    {F : SWF Voter Alt}
    {i j : Voter} {x y z w : Alt}
    (hij : i ≠ j)
    (h1 : RightAtomSemantics F i x y)
    (h2 : RightAtomSemantics F j z w) :
    MINLIB F := ...
```

Expected proof:

- unpack `RightAtomSemantics` into endpoint inequalities and `Decisive`;
- instantiate the existential witnesses in `MINLIB`.

This theorem would show that a fixed two-rights package is sufficient for Lean
`MINLIB`.
It would not prove that all `MINLIB` instances are represented by M4 witness
packages.
It would not prove the selector-free encoding equivalent to `MINLIB`.

Recommendation:
Treat this as optional Level B+.
The required Level B bridge is the right-atom orientation lemma.

## 10. What This Would Prove

If implemented later, Level B would prove:

- a Lean semantic predicate for M4 right atoms is aligned with `Decisive`;
- the unordered-pair orientation convention is Lean-backed via
  `Decisive.symm`;
- optionally, two fixed right atoms with distinct voters imply Lean `MINLIB`.

This strengthens the semantic target of M4 without changing the finite-data
certificate.

## 11. What This Would Not Prove

Level B would not prove:

- Python `_right_clauses` correctness;
- `FiniteSchema` correctness;
- SAT assignment semantics;
- semantic-to-CNF correctness;
- CNF artifact correctness;
- checker correctness;
- full equivalence between selector-free fixed-witness packages and `MINLIB`;
- necessity direction from `MINLIB` to fixed witness package;
- Mask-Shape Collapse Law structural necessity;
- general Sen theorem;
- family-scale theorem.

## 12. Implementation Sketch

Potential future Lean sketch:

```lean
import SocialChoiceAtlas.Axioms.Liberalism

namespace SocialChoiceAtlas

universe u v
variable {Voter : Type u} {Alt : Type v}
variable [DecidableEq Alt] [Fintype Alt]

def RightAtomSemantics (F : SWF Voter Alt) (i : Voter) (x y : Alt) : Prop :=
  x ≠ y ∧ Decisive F i x y

theorem rightAtomSemantics_symm
    {F : SWF Voter Alt} {i : Voter} {x y : Alt}
    (h : RightAtomSemantics F i x y) :
    RightAtomSemantics F i y x := by
  constructor
  · exact h.1.symm
  · exact Decisive.symm h.2

theorem rightAtomSemantics_iff_swap
    {F : SWF Voter Alt} {i : Voter} {x y : Alt} :
    RightAtomSemantics F i x y ↔ RightAtomSemantics F i y x := by
  constructor
  · exact rightAtomSemantics_symm
  · exact rightAtomSemantics_symm

-- Optional Level B+
theorem twoRightAtoms_imply_MINLIB
    {F : SWF Voter Alt}
    {i j : Voter} {x y z w : Alt}
    (hij : i ≠ j)
    (h1 : RightAtomSemantics F i x y)
    (h2 : RightAtomSemantics F j z w) :
    MINLIB F := by
  refine ⟨i, j, hij, x, y, z, w, ?_, ?_, ?_, ?_⟩
  · exact h1.1
  · exact h2.1
  · exact h1.2
  · exact h2.2

end SocialChoiceAtlas
```

This sketch may need minor adjustment to match actual Lean syntax and
existing universe/import conventions.
It is a design target, not an executed proof.

## 13. Acceptance Criteria for a Later Lean PR

A later Lean PR should be accepted only if:

- it introduces a small semantic-only bridge file;
- it proves the orientation lemma;
- it does not import SAT/CNF/checker artifacts;
- it does not claim `_right_clauses` correctness;
- it does not claim semantic-to-CNF correctness;
- it does not alter existing `Decisive` or `MINLIB` definitions;
- it builds with `lake build` or a targeted Lean check;
- it updates docs to say Level B is implemented, while Level C remains future
  work.

## 14. Forbidden Scope

Forbidden in the later Level B implementation:

- modifying `Decisive`;
- modifying `MINLIB`;
- modifying Python encoders;
- proving or claiming CNF correctness;
- importing generated artifacts;
- proving Mask-Shape Collapse Law;
- proving general Sen theorem;
- proving family-scale theorem;
- changing M4 finite-data certificates.

## 15. Claim Language After Implementation

If Level B is implemented, allowed claim language:

- The M4 right-atom semantic target is Lean-backed.
- The unordered-pair convention for right atoms is supported by a Lean
  orientation lemma.
- A fixed two-rights package may be shown sufficient for Lean `MINLIB` if the
  optional theorem is included.

Still forbidden:

- The Python right-clause generator is Lean-proved correct.
- The M4 CNF artifacts are Lean-proved correct.
- The full selector-free encoding is Lean-proved equivalent to `MINLIB`.
- M4 proves semantic-to-CNF correctness.

## 16. Risks and Reviewer Questions

Risk 1:
If `RightAtomSemantics` is merely an abbreviation for `Decisive`, the bridge
may look cosmetic.

Mitigation:
include endpoint distinctness and the orientation lemma as the substantive
content.

Risk 2:
Reviewers may still ask whether `_right_clauses` are correct.

Mitigation:
state clearly that this is Level C, not Level B.

Risk 3:
The optional two-rights lemma may be mistaken for full `MINLIB` equivalence.

Mitigation:
state it is only a sufficient direction for fixed witnesses.

## 17. Next Authorized Action

The next authorized action is review of this Level B design note.

If approved later, a separate Lean PR may implement only the small
semantic-only bridge described here. This document does not authorize Lean
implementation, Python changes, solver reruns, checker reruns, 3-voter work,
warrant-contract implementation, paper-claim promotion, or Level C artifact
correctness work.

## Lean Implementation Follow-up

The Level B semantic bridge has been implemented in:

`SocialChoiceAtlas/Sen/RightAtomBridge.lean`

Implemented:

- `RightAtomSemantics`;
- `rightAtomSemantics_symm`;
- `rightAtomSemantics_iff_swap`;
- optional Level B+ `twoRightAtoms_imply_MINLIB`.

Scope remains Level B only:

- no Python `_right_clauses` correctness;
- no `FiniteSchema` correctness;
- no SAT assignment semantics;
- no semantic-to-CNF correctness;
- no full `MINLIB` equivalence;
- no Mask-Shape Collapse Law proof.

See `docs/m4_right_atom_decisive_bridge_lean_result.md`.
