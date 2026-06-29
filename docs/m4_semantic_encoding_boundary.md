# M4 Semantic Encoding Boundary

Status: claim-boundary / docs-only
Depends on: M4 finite-data closure note
Current authorization: semantic encoding boundary only
Not authorized: Lean theorem, encoding-correctness theorem, solver rerun, checker rerun, 3-voter run, warrant-contract implementation, paper-claim promotion

## 1. Purpose

This document fixes the semantic boundary for M4 after finite-data closure.

M4's finite-data certificate is a certificate inside the declared
selector-free semantic encoding. It does not by itself prove that the encoding
is a faithful formalization of Sen's liberal paradox in Lean.

The goal is to make the encoding assumption explicit, auditable, and
front-loaded rather than hidden as a caveat.

## 2. Boundary Decision

Decision:
M4 should state its main finite-data claim under the declared selector-free
semantic encoding.

The finite-data certificate proves internal facts about that declared
encoding:

- 48-cell phase diagram coverage;
- SAT-cell RepairEmpty;
- UNSAT-cell orbit-fiber exactness;
- shape-blind support truncation;
- non-circularity.

The correspondence between this encoding and the Lean/Sen notion of
decisiveness is an auditable assumption, not yet a Lean-proved bridge theorem.

## 3. Two-Layer Claim Discipline

Layer 1: Internal finite-data theorem/certificate.

```text
Proven by machine-checked finite artifact verification.
Assumes the declared selector-free semantic encoding as the object of study.
```

Layer 2: Encoding correctness / Sen-faithfulness.

```text
The claim that the declared encoding faithfully represents the intended Sen24
social-choice structure.
This is currently an audited assumption, not a proved theorem.
```

M4 may claim Layer 1.
M4 must not claim Layer 2 as proved.

## 4. Declared Selector-Free Semantic Encoding

The M4 encoding uses:

- fixed `n=2`, `m=4` Sen24 universe;
- bundled residual masks over `asymm`, `un`, `minlib`, `no_cycle3`,
  `no_cycle4`;
- selector-free semantic atoms;
- base atoms for ordinary residual axioms;
- `right(voter,pair)` atoms for fixed-witness liberal rights;
- obstruction shapes `O2`/`O3`/`O4` computed from witness pair overlap.

This encoding intentionally avoids using the production `minlib` selector as a
MUS unit.
It is an exploratory selector-free semantic encoding used for the M4
finite-data audit.

## 5. `right(voter,pair)` and Lean `Decisive`

Lean-side reference:
`SocialChoiceAtlas/Axioms/Liberalism.lean` defines `Decisive F i x y` as the
condition that, for every profile, if voter `i` prefers `x` to `y` then
society strictly prefers `x` to `y`, and if voter `i` prefers `y` to `x` then
society strictly prefers `y` to `x`. `MINLIB` requires two distinct voters,
each decisive over some pair.

Script-side reference:
`scripts/exploration/m4/semantic_mus_precheck.py` defines
`right_atom(voter,pair)` as a canonical unordered pair label and encodes it by
requiring, for every profile, the social pairwise variable to follow that
voter's preference on the declared pair.

Therefore:
`right(voter,{a,b})` is structurally aligned with Lean
`Decisive F voter a b`, up to the unordered-pair convention and Lean's
`Decisive.symm`.

Current status:
This is a documented semantic alignment, not a Lean-proved equivalence theorem.

## 6. Relation to Legacy Selector Encodings

The legacy `decisive_voter0.py` and `decisive_voter1.py` encodings use
selector variables and guarded implications:

```text
selector(pair) -> social pairwise preference follows the selected voter's
preference.
```

The M4 `right(voter,pair)` atom is a selector-free fixed-witness
specialization:

```text
the pair and voter are fixed by the witness configuration, so no existential
selector is used as a repair atom.
```

This supports auditability but does not itself prove semantic equivalence to
Lean `Decisive`.

## 7. What Is Auditable Now

Currently auditable:

- the Lean definition of `Decisive` and `MINLIB`;
- the script-level construction of `right_atom`;
- the per-profile clause pattern forcing social preference to follow the
  declared voter's preference;
- the use of canonical unordered alternative pairs;
- the two-rights fixed-witness package used for minlib-active cells;
- the exclusion of one-sided minlib packages from the ambient M4 theory;
- the non-circular treatment of `Shape(W)` as an analysis coordinate, not part
  of `T` identity.

## 8. What Is Not Yet Proved

Not yet proved:

- Lean theorem: `right_atom(voter,pair)` is equivalent to
  `Decisive F voter x y`;
- Lean theorem: the selector-free fixed-witness encoding is equivalent to
  `MINLIB`;
- semantic-to-CNF correctness theorem for the M4 artifacts;
- general Sen theorem;
- family-scale theorem;
- structural necessity of the Mask-Shape Collapse Law.

## 9. Claim Language

Allowed language:

```text
Under the declared selector-free semantic encoding, we machine-verify...
Within the declared Sen24 encoding, the phase diagram satisfies...
Assuming the declared encoding as the audited object of study, Certificate 2
closes the finite-data side...
The right atoms are structurally aligned with Lean decisiveness, but the
bridge is not yet theorem-proved.
```

## 10. Forbidden Language

Forbidden language:

```text
We prove Sen's theorem has this repair geometry.
We prove in Lean that right atoms are Decisive.
The encoding correctness is established.
The phase diagram is a general theorem of social choice.
M4 proves a general Sen theorem.
M4 proves semantic-to-CNF correctness.
```

## 11. Track X Consequence

For Track X, the paper should front-load this boundary.

The first statement of the contribution should be about the declared encoding
and its audited phase diagram, not about Sen's theorem in unrestricted form.

Lean or proof-carrying packaging in Track X should be understood as packaging
the finite-data certificate, not as proving encoding correctness unless a
separate bridge theorem is later added.

Track X may later add a minimal bridge theorem as a strengthening step, but
this boundary document does not authorize Lean work.

## 12. Track Y / Future Bridge Theorem

Track Y may later pursue bridge theorems:

- Lean bridge: `right_atom` semantics corresponds to `Decisive`;
- fixed-witness minlib package corresponds to a scoped instance of `MINLIB`;
- semantic-to-CNF correctness for the generated artifacts;
- structural explanation of the Mask-Shape Collapse Law.

These are optional future work and are not required for M4 finite-data
closure.

## 13. Non-Claims

This boundary document does not claim:

- Lean theorem;
- encoding-correctness theorem;
- semantic-to-CNF correctness theorem;
- general Sen theorem;
- Arrow theorem;
- Gibbard-Satterthwaite theorem;
- 3-voter theorem;
- family-scale theorem;
- structural necessity of the Mask-Shape Collapse Law;
- that the script-level `right` atom is already theorem-proved equivalent to
  Lean `Decisive`;
- that Track X Lean packaging, by itself, proves encoding correctness.

## 14. Next Authorized Action

The next authorized action is review of this semantic encoding boundary.

After review, Track X may use this boundary as front-loaded claim language for
the M4 finite-data result. No Lean theorem, encoding-correctness theorem,
solver rerun, checker rerun, 3-voter run, warrant-contract implementation, or
paper-claim promotion is authorized by this document.

## 15. Bridge Feasibility Follow-up

A follow-up feasibility note evaluates the possible bridge between M4
`right_atom` semantics and Lean `Decisive`.

Current status:

- Level A documentation bridge: achieved;
- Level B Lean semantic predicate bridge: feasible next target;
- Level C full artifact bridge: not yet ready.

See `docs/m4_right_atom_decisive_bridge_feasibility.md`.

## 16. Level B Bridge Design Follow-up

A Level B design note specifies a minimal Lean semantic bridge for the central
right atom.
The design remains semantic-only and does not claim Python clause correctness
or semantic-to-CNF correctness.

See `docs/m4_right_atom_decisive_bridge_design.md`.

## 17. Level B Implementation Follow-up

The central M4 right-atom semantic target is now Lean-backed by a small Level B
bridge.

This does not prove:

- Python clause correctness;
- CNF artifact correctness;
- semantic-to-CNF correctness;
- full selector-free encoding equivalence to `MINLIB`.

Level C remains future work.

See `docs/m4_right_atom_decisive_bridge_lean_result.md`.
