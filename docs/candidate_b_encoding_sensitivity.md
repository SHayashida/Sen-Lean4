# Candidate B: Encoding Sensitivity (M2.1)
## Repair-candidate representation non-canonicity after transfer

**Milestone:** M2.1
**Branch intent:** `codex/m2.1-candidate-b`
**Status:** Witness-class design memo (no generators or scripts yet).
**Related:** [docs/candidate_b_minlib_granularity.md](candidate_b_minlib_granularity.md),
[docs/m2_scope_wall.md](m2_scope_wall.md),
[docs/no_cycle_interpretation_note.md](no_cycle_interpretation_note.md),
[docs/axiom_semantics_scaling.md](axiom_semantics_scaling.md)

This document defines the M2.1 witness class **before** any generator or script is
added. It must be reviewed before prototypes are written.

---

## What belongs to M2, not M2.1

Status and impossibility transfer is **M2 work, not M2.1 work**.

M2 already handles the transfer of the legitimization / impossibility guarantee.
The M2 Proof layer establishes the semantic Sen impossibility lift through the
kernel-checked theorem `sen_impossibility_lifts` in
`SocialChoiceAtlas/Sen/Lifting/ImpossibilityLift.lean`, and the M2 scope wall
records exactly how far that transfer reaches (see
[docs/m2_scope_wall.md](m2_scope_wall.md)).

M2.1 does **not** re-open status/impossibility transfer. It assumes M2's transfer
result as settled and asks a different question one layer down.

---

## What M2.1 studies

M2.1 studies **repair-candidate representation granularity after transfer**.

The object under study is not whether the impossibility transfers — M2 owns that —
but whether the *representation* of repair candidates remains non-canonical once
the same impossibility is instantiated at larger finite cases.

### M2.1 core question

> Does the M1.5 bundled/split repair-presentation non-canonicity persist after
> transfer to larger finite cases?

This is a question about repair-candidate representation, not about status or
impossibility transfer.

---

## Base-case seed (reused from M1.5)

M2.1 reuses the M1.5 bundled/split non-canonicity result as its base-case seed
(see [docs/candidate_b_minlib_granularity.md](candidate_b_minlib_granularity.md)).

At the base case `(n,m) = (2,4)`, inside the restricted local-rationality family
defined by `no_cycle3` and `no_cycle4`, M1.5 established:

- the bundled and split representations are clause-set equivalent under the
  intended mapping `minlib ↔ decisive_voter0 ∧ decisive_voter1`;
- they share the same UNSAT frontier under that mapping;
- yet the bundled minimal repair `{minlib}` refines into split person-specific
  minimal repairs `{decisive_voter0}` and `{decisive_voter1}`.

So at the base case, the repair explanation already changes under pure
granularity refinement, with the stronger-encoding explanation explicitly ruled
out by clause-set equivalence. This base-case non-canonicity is the seed; M2.1
asks whether it survives transfer to larger finite cases.

---

## Family-scale witness class

A **family-scale Candidate-B witness** for M2.1 is a tuple

    W = ( case, bundled_pkg, split_pkg, map, repairs_bundled, repairs_split )

satisfying all of the following conditions:

1. **Case.** `case = (n,m)` is one of the specified larger cases below, strictly
   beyond the `(2,4)` base case.
2. **Representations.** `bundled_pkg` is drawn from the bundled lever universe
   `{asymm, un, minlib, no_cycle3, no_cycle4}`; `split_pkg` is the corresponding
   package in the split lever universe
   `{asymm, un, decisive_voter0, decisive_voter1, no_cycle3, no_cycle4}` obtained
   by replacing `minlib` with `decisive_voter0 ∧ decisive_voter1`.
3. **Transport map.** `map` is the explicit correspondence
   `minlib ↔ decisive_voter0 ∧ decisive_voter1` lifted to the case `(n,m)`,
   recorded so that bundled and split repairs can be compared lever-by-lever.
4. **Equivalence control.** The mapped bundled and split packages must remain
   satisfiability-equivalent at `(n,m)`; clause-set equivalence under the map is
   recorded when it holds and flagged when it does not, so that any observed
   repair divergence cannot be silently attributed to a stronger split encoding.
5. **Repair sets.** `repairs_bundled` and `repairs_split` are the
   inclusion-minimal repair (MCS) sets enumerated at `(n,m)` for the bundled and
   split packages respectively.
6. **Non-canonicity signal.** The witness is *positive* when the bundled and
   split repair sets disagree as representations of the same transferred
   impossibility — e.g. a bundled `{minlib}` repair has no single-lever split
   image, or the split side exposes person-specific repairs with no bundled
   counterpart.

All M2.1 witnesses are interpreted strictly inside the restricted
local-rationality family `no_cycle3 ∧ no_cycle4`. A family-scale witness is a
statement about repair-candidate representation at the witness layer; it is not a
claim about full `SocialAcyclic`, and it is not a family-level CNF certificate.

---

## Initial larger cases

The first M2.1 witnesses target the two smallest finite cases beyond the base:

- `(n,m) = (2,5)`
- `(n,m) = (3,4)`

These are the same neighboring cases used by the earlier liftability work, so the
parametric generator and auditor are already known to cover them. At `m = 5` the
conjunction `no_cycle3 ∧ no_cycle4` still permits length-5 cycles, so the
`(2,5)` case is interpreted only within the local-rationality family and carries
the Step 0.5 scope caveat (see
[docs/no_cycle_interpretation_note.md](no_cycle_interpretation_note.md)).

---

## Required new artifacts

The M2.1 witness class requires the following new artifacts. None exist yet; this
list scopes what the reviewed prototype is allowed to produce.

1. **Bundled/split family-scale encodings.** Bundled and split CNFs (or
   equivalent encodings) generated at `(2,5)` and `(3,4)`.
2. **Repair enumeration outputs.** Inclusion-minimal repair (MCS) enumerations
   for each bundled and split package at each larger case.
3. **Transport map.** An explicit, machine-readable record of the
   `minlib ↔ decisive_voter0 ∧ decisive_voter1` correspondence at each case,
   used to align bundled and split repairs.
4. **Comparison report.** A report that pairs bundled and split repair sets
   under the transport map and classifies each pair as canonical-preserving or
   non-canonical at family scale.
5. **Scope statement.** A statement distinguishing local-rationality
   (`no_cycle3 ∧ no_cycle4`) from full `SocialAcyclic`, attached to every
   comparison output, so that no artifact is mistaken for a full-acyclicity or
   family-level CNF certificate.

---

## Prototype location

Until the artifact schema stabilizes, all M2.1 prototypes must live under:

- `scripts/exploration/candidate_b/`

Nothing under `scripts/` (top level) may be added for M2.1 while the schema is
still in flux.

## Promotion criteria

Promotion of a prototype from `scripts/exploration/candidate_b/` to `scripts/`
requires all of:

- a stable CLI,
- a schema / manifest definition,
- reproducible output paths,
- smoke coverage.

---

## M2 / M2.1 split (preserved)

The M2 / M2.1 boundary is preserved explicitly:

- **M2** = transfer of the legitimization / impossibility guarantee.
- **M2.1** = transfer of repair-candidate representation non-canonicity.

M2 settles *whether* the impossibility transfers. M2.1 studies *how the repair
candidates are represented* once it has transferred. M2.1 does not restate,
weaken, or extend any M2 status/impossibility transfer claim.

---

## Do-not-modify list

M2.1 must not modify any of the following:

- `SocialChoiceAtlas/Sen/Lifting/ImpossibilityLift.lean`,
- the theorem `sen_impossibility_lifts`,
- any M2 theorem statements,
- any M2 paper claims,
- the baseline CNF / LRAT certificates.

---

## Wording discipline

To keep M2.1 claims accurate:

- Do not state that `UN ∧ MINLIB` implies `4 ≤ m`. The hypothesis `4 ≤ m` is an
  assumption of the M2 lift theorem, not a consequence of the axioms.
- Do not conflate `no_cycle3 ∧ no_cycle4` with full `SocialAcyclic`. The
  short-cycle conjunction defines a local-rationality family only.
- Do not claim the sen24 CNF witness is a family-level CNF certificate. It
  certifies the audited short-cycle encoding at the base case.
- Do not treat M2.1 as status/impossibility transfer. That is M2.
- M2.1 is about repair-candidate representation granularity after transfer.
