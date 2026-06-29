# M4 Right-Atom Lean Bridge Result

Status: Level B implemented / semantic-only

Implemented file:
`SocialChoiceAtlas/Sen/RightAtomBridge.lean`

Implemented definitions and theorems:

- `RightAtomSemantics`;
- `rightAtomSemantics_symm`;
- `rightAtomSemantics_iff_swap`;
- `twoRightAtoms_imply_MINLIB`.

Validation:

- `lake env lean SocialChoiceAtlas/Sen/RightAtomBridge.lean`: passed;
- `lake build SocialChoiceAtlas.Sen.RightAtomBridge`: passed;
- `lake build`: passed, with pre-existing linter warnings outside the new
  bridge file.

Scope:

This is a Level B semantic bridge only. It provides a Lean semantic target for
the central M4 right atom and proves orientation invariance for unordered-pair
use.

Non-claims:

- no Python `_right_clauses` correctness;
- no `FiniteSchema` correctness;
- no SAT assignment semantics;
- no semantic-to-CNF correctness;
- no CNF artifact correctness;
- no full `MINLIB` equivalence;
- no general Sen theorem;
- no family-scale theorem;
- no Mask-Shape Collapse Law proof.
