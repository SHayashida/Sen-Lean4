# M4 Bridge Feasibility: `right_atom` and Lean `Decisive`

Status: bridge-feasibility / docs-only
Depends on: M4 semantic encoding boundary
Current authorization: feasibility note only
Not authorized: Lean theorem, encoding-correctness theorem, solver rerun, checker rerun, 3-voter run, warrant-contract implementation, paper-claim promotion

## 1. Purpose

This document evaluates whether the M4 `right(voter,pair)` atom can be
bridged to Lean `Decisive`.

The goal is not to implement the bridge theorem here.
The goal is to identify the minimal theorem target, required representation
objects, and remaining proof obligations.

This note follows the semantic boundary decision: M4 currently has an internal
finite-data certificate under a declared selector-free semantic encoding,
while encoding correctness remains an audited assumption.

## 2. Current Boundary

Current status:

- `right(voter,pair)` is structurally aligned with Lean `Decisive`.
- The alignment is documented in `docs/m4_semantic_encoding_boundary.md`.
- There is not yet a Lean theorem proving equivalence.
- Track X may later add a minimal bridge theorem as a strengthening step.

## 3. Source Definitions Inspected

Inspected:

- `SocialChoiceAtlas/Axioms/Liberalism.lean`: defines `Decisive`, `MINLIB`,
  and `Decisive.symm`.
- `scripts/exploration/m4/semantic_mus_precheck.py`: defines canonical
  unordered pairs, `right_atom`, `_right_clauses`, `atom_clauses`, and
  obstruction shape via pair overlap.
- `encoding/schema.py`: defines social pairwise variables `var_p`, profile
  preference lookup `prefers`, voter-specific helpers `pref0`/`pref1`, and
  legacy/parametric minlib selector modes.
- `encoding/axioms/decisive_voter0.py`: legacy selector encoding for voter 0;
  it selects a pair and guards clauses forcing social pairwise preference to
  follow voter 0.
- `encoding/axioms/decisive_voter1.py`: legacy selector encoding for voter 1;
  it selects a pair and guards clauses forcing social pairwise preference to
  follow voter 1.
- `docs/m4_semantic_encoding_boundary.md`: records the claim boundary that
  M4's finite-data result is internal to the declared selector-free semantic
  encoding.
- `docs/m4_finite_data_closure_note.md`: records finite-data closure under
  the declared encoding and separates Track X from optional Track Y.

## 4. Lean-Side Target

Lean target:
`Decisive F i x y` says that for every profile:

- if voter `i` prefers `x` to `y`, then society strictly prefers `x` to `y`;
- if voter `i` prefers `y` to `x`, then society strictly prefers `y` to `x`.

`MINLIB F` requires two distinct voters, each decisive over some pair.

`Decisive.symm` already records that decisiveness is invariant under reversing
the pair orientation.

The natural Lean-side bridge target is not full `MINLIB` immediately.
The minimal target is a fixed voter / fixed unordered pair bridge:

```text
M4 right-atom semantics for (i,{x,y}) corresponds to Decisive F i x y,
up to pair orientation.
```

## 5. Script-Side Source

Script target:
`right_atom(voter,pair)` creates a canonical unordered-pair label.
`_right_clauses(schema,voter,pair)` emits one unit clause per finite profile.
For each profile, the emitted social pairwise literal follows the declared
voter's preference on that pair.

This is selector-free:
the voter and pair are fixed by the witness configuration.
No existential minlib selector is used as the repair atom.

## 6. Semantic Alignment

The alignment is conceptually direct:

```text
Lean Decisive F i x y:
  for every profile p, individual preference by voter i on x/y implies the
  same social strict preference.

M4 right_atom(i,{x,y}) clauses:
  for every finite profile p, the social pairwise variable is forced to match
  voter i's preference on x/y.
```

Thus, under a representation map from Lean profiles/SWF values to
`FiniteSchema` profile indices and SAT social-pair variables, the right atom
has the same intended semantics as `Decisive`.

The phrase "under a representation map" is essential.
Without that map, the current repository has semantic alignment but not a
formal bridge theorem.

## 7. Missing Bridge Objects

To prove a Lean bridge theorem, the repository needs explicit bridge objects
connecting:

1. Profile representation:
   Lean `Profile Voter Alt` or equivalent profile object
   to `FiniteSchema.profiles[p]` index.

2. Individual preference:
   Lean `prefers_i p i x y`
   to Python `schema.prefers(p,i,x,y)`.

3. Social preference:
   Lean `strictPart (F p) x y`
   to SAT assignment truth of `schema.var_p(p,x,y)`.

4. SWF representation:
   Lean `F : SWF Voter Alt`
   to assignment/function over all `var_p(p,a,b)` variables.

5. Clause semantics:
   satisfaction of all `_right_clauses(schema,i,{x,y})`
   to the profile-wise implications required by `Decisive`.

6. Unordered-pair convention:
   M4 canonical pair `{x,y}`
   to Lean ordered pair `x y`, with orientation handled by `Decisive.symm`.

These bridge objects do not appear to be established yet as Lean
definitions/theorems in the current M4 track.

## 8. Candidate Bridge Levels

### Level A: Documentation bridge

Level A records the conceptual alignment between `right_atom` and `Decisive`.
It is already achieved by the semantic boundary and this feasibility note.
It does not strengthen theorem status.

### Level B: Lean semantic predicate bridge

Level B would define a Lean-side finite semantic predicate, for example:

```text
RightSemantics F i x y := Decisive F i x y
```

or a pair-symmetric variant.
It would prove orientation lemmas using `Decisive.symm`.
This verifies the intended mathematical target but does not connect to Python
clauses or CNF artifacts.

### Level C: Full artifact bridge

Level C would connect `FiniteSchema` profiles, SAT variables,
`_right_clauses`, assignments, and Lean `Decisive`.
This is a semantic-to-artifact correctness theorem.
It is substantially heavier and should not be attempted before Level B.

## 9. Minimal Viable Bridge Theorem

Recommended minimal viable bridge:
a Lean-level fixed-voter/fixed-pair semantic bridge, not a full CNF
correctness theorem.

Candidate theorem shape:

For finite Sen24 voters and alternatives, define a Lean predicate representing
the M4 right atom at the semantic level:

```text
RightAtomSemantics F i x y := Decisive F i x y
```

Then prove:

```text
RightAtomSemantics F i x y <-> RightAtomSemantics F i y x
```

or:

```text
RightAtomSemantics F i x y <-> Decisive F i x y
```

depending on whether the predicate is introduced as an abbreviation or
nontrivial wrapper.

This would formally justify the unordered-pair convention used by M4 right
atoms, via `Decisive.symm`.

This Level B theorem would not prove that Python `_right_clauses` are correct.
It would, however, give Track X a Lean-backed semantic target for the central
right atom.

## 10. What Would Not Yet Be Proved

Even after the minimal Level B bridge, the following would remain unproved:

- Python `_right_clauses` correctness;
- `FiniteSchema` profile enumeration correctness;
- SAT variable assignment semantics;
- semantic-to-CNF correctness;
- full selector-free fixed-witness encoding equivalence to `MINLIB`;
- Mask-Shape Collapse Law structural necessity;
- general Sen theorem;
- family-scale generalization.

## 11. Feasibility Verdict

Verdict: FEASIBLE AS LEVEL B, NOT YET FEASIBLE AS LEVEL C.

A minimal Lean semantic bridge appears feasible because Lean already defines
`Decisive`, `MINLIB`, and `Decisive.symm`.

A full artifact bridge is not yet ready because the representation map between
Lean profiles/SWFs and `FiniteSchema` / SAT variables is not yet formalized.

## 12. Recommended Next Step

Recommended next step:
create a Lean bridge design note or small Lean target for Level B only.

Do not attempt full semantic-to-CNF correctness yet.

The next authorized implementation, if approved later, should introduce only a
minimal Lean semantic bridge around the central right atom and pair
orientation.

Potential future file names, not created by this note:

```text
docs/m4_right_atom_decisive_bridge_design.md
SocialChoiceAtlas/Sen/RightAtomBridge.lean
```

## 13. Claim Language After the Bridge

If Level B is later implemented, allowed claim language may become:

```text
The M4 right-atom semantics is backed by a Lean-level decisiveness predicate
and orientation lemma.
```

It still must not become:

```text
The Python encoding is Lean-proved correct.
The CNF artifacts are Lean-proved correct.
M4 proves semantic-to-CNF correctness.
```

## 14. Non-Claims

This feasibility note does not claim:

- Lean theorem implemented;
- `right_atom` equivalent to `Decisive` already proved;
- Python `_right_clauses` correctness;
- `FiniteSchema` correctness;
- SAT assignment semantics correctness;
- semantic-to-CNF correctness;
- full `MINLIB` bridge;
- Mask-Shape Collapse Law structural necessity;
- general Sen theorem;
- family-scale theorem.

## 15. Next Authorized Action

The next authorized action is review of this feasibility note.

If approved later, the next implementation should target only the Level B
Lean semantic predicate bridge. No Lean theorem, encoding-correctness theorem,
solver rerun, checker rerun, 3-voter work, warrant-contract implementation,
or paper-claim promotion is authorized by this document.

## Design Follow-up

A follow-up design note specifies the intended Level B Lean semantic bridge:

- `RightAtomSemantics` with distinct-endpoint discipline;
- orientation lemma using `Decisive.symm`;
- optional fixed-two-rights sufficiency lemma for `MINLIB`.

See `docs/m4_right_atom_decisive_bridge_design.md`.

## Level B Implementation Follow-up

A small Level B Lean semantic bridge has been implemented.

This upgrades the bridge status from:

- Level A documentation bridge only

to:

- Level B semantic target implemented.

Level C full artifact bridge remains future work.

See `docs/m4_right_atom_decisive_bridge_lean_result.md`.
