/-
Copyright (c) 2025 SocialChoiceAtlas Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SocialChoiceAtlas Contributors
-/

import SocialChoiceAtlas.Axioms.Liberalism

/-!
# M4 Right-Atom Bridge

This file provides the small Level B semantic bridge between the M4
selector-free `right(voter,{x,y})` atom and the existing Lean notion
`Decisive`.

Scope:
- semantic-only;
- no SAT/CNF artifacts;
- no Python clause correctness;
- no semantic-to-CNF correctness;
- no general Sen/family-scale theorem.
-/

namespace SocialChoiceAtlas

universe u v

variable {Voter : Type u} {Alt : Type v}
variable [DecidableEq Alt] [Fintype Alt]

/--
Semantic target for the M4 right atom.

`RightAtomSemantics F i x y` means that the endpoints are distinct and
voter `i` is decisive over the ordered pair `(x,y)`.

The explicit `x ≠ y` component mirrors the M4 script-side `canonical_pair`
discipline, where right atoms are generated only for distinct endpoints.
-/
def RightAtomSemantics (F : SWF Voter Alt) (i : Voter) (x y : Alt) : Prop :=
  x ≠ y ∧ Decisive F i x y

/--
Orientation invariance for the semantic right atom.

This is the core Level B bridge: M4 right atoms are indexed by unordered
alternative pairs, while Lean `Decisive` is stated for ordered pairs.
-/
theorem rightAtomSemantics_symm
    {F : SWF Voter Alt} {i : Voter} {x y : Alt}
    (h : RightAtomSemantics F i x y) :
    RightAtomSemantics F i y x := by
  constructor
  · exact h.1.symm
  · exact Decisive.symm h.2

/--
Bidirectional orientation invariance for the semantic right atom.
-/
theorem rightAtomSemantics_iff_swap
    {F : SWF Voter Alt} {i : Voter} {x y : Alt} :
    RightAtomSemantics F i x y ↔ RightAtomSemantics F i y x := by
  constructor
  · intro h
    exact rightAtomSemantics_symm h
  · intro h
    exact rightAtomSemantics_symm h

/--
Optional Level B+ lemma.

Two fixed right atoms for distinct voters are sufficient for Lean `MINLIB`.

This is only a sufficient direction for fixed witnesses. It does not prove
that all `MINLIB` instances are represented by M4 witness packages, and it
does not prove the selector-free encoding equivalent to `MINLIB`.
-/
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
