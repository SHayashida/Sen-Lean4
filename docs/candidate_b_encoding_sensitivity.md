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

- the bundled and split representations are clause-multiset equivalent (≡CM)
  under the repair-transport map `π(minlib) = {decisive_voter0, decisive_voter1}`;
- they share the same UNSAT frontier under that map;
- yet the bundled minimal repair `{minlib}` refines into split person-specific
  minimal repairs `{decisive_voter0}` and `{decisive_voter1}`.

So at the base case, the repair explanation already changes under pure
granularity refinement, with the stronger-encoding explanation explicitly ruled
out by clause-multiset equivalence (≡CM). This base-case non-canonicity is the
seed; M2.1 asks whether it survives transfer to larger finite cases.

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
   by applying the repair-transport map `π` (below) to each bundled lever.
3. **Transport map.** `map` is the explicit repair-transport map `π` lifted to
   the case `(n,m)`. It maps the bundled `minlib` lever to its split counterparts
   and carries every shared lever to its singleton counterpart:

   - `π(minlib) = {decisive_voter0, decisive_voter1}`
   - `π(asymm) = {asymm}`
   - `π(un) = {un}`
   - `π(no_cycle3) = {no_cycle3}`
   - `π(no_cycle4) = {no_cycle4}`

   `π` records lever correspondence and repair transport, not a logical
   equivalence between axiom formulas. It is recorded so that bundled and split
   repairs can be compared lever-by-lever.
4. **Equivalence control.** The mapped bundled and split packages must remain
   satisfiability-equivalent at `(n,m)`; clause-multiset equivalence (≡CM) under
   `π` is recorded when it holds and flagged when it does not, so that any
   observed repair divergence cannot be silently attributed to a stronger split
   encoding. Whether ≡CM persists at family scale is settled first by Step 0
   below, before any repair enumeration.
5. **Repair sets.** `repairs_bundled` and `repairs_split` are the
   inclusion-minimal repair (MCS) sets enumerated at `(n,m)` for the bundled and
   split packages respectively.
6. **Non-canonicity signal.** The non-canonicity signal is present when the
   bundled and split repair sets disagree as representations of the same
   transferred impossibility — e.g. a bundled `{minlib}` repair has no
   single-lever split image, or the split side exposes person-specific repairs
   with no bundled counterpart. A Candidate-B witness is successful when this
   signal is present under a Step-0-confirmed equivalence relation.

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

## Step 0: ≡CM persistence check

Before any full repair enumeration, M2.1 first checks whether the M1.5
clause-multiset-equivalence (≡CM) structure persists at family scale. The M1.5
result was strong precisely because the bundled and split base-case packages
were ≡CM, which ruled out logical-strength explanations of the repair
divergence. M2.1 must not assume that shield survives transfer; it must measure
it.

Consequently, **the first prototype is not the full repair comparator.** The
first prototype is an ≡CM checker for the bundled/split packages at:

- `(n,m) = (2,5)`
- `(n,m) = (3,4)`

The prototype generates the bundled and split packages under the repair-transport
map `π` and produces a comparison report analogous to the M1.5
`comparison.json`. For each case it must classify the bundled/split pair as
exactly one of:

1. **≡CM persists** — bundled and split packages are clause-multiset equivalent
   under `π`.
2. **satisfiability-equivalent but not ≡CM** — the packages share SAT/UNSAT
   status under `π` but their clause multisets differ.
3. **status diverges** — bundled and split packages disagree on SAT/UNSAT status
   under `π`.
4. **comparison inconclusive / generation failed** — the comparison artifact
   could not be produced or validated.

### Step 0 interpretation rules

- **If ≡CM persists:** M2.1 may proceed with the strong M1.5-style claim —
  repair-candidate non-canonicity persists even under clause-multiset-equivalent
  re-encodings.
- **If only satisfiability-equivalence persists:** M2.1 must weaken its claim —
  repair-candidate representation differs under satisfiability-equivalent
  encodings, but the M1.5 clause-multiset-equivalence shield no longer rules out
  logical-strength explanations.
- **If status diverges:** M2.1 must not claim repair-representation
  non-canonicity for that case. Record it instead as an encoding-transfer
  boundary, or as a negative result about the persistence of the M1.5 witness
  class.
- **If comparison is inconclusive:** do not proceed to repair enumeration for
  that case until the comparison artifact is repaired.

### Gate before repair enumeration

Repair enumeration is **not authorized until Step 0 has been reviewed.**

If ≡CM fails (cases 2, 3, or 4 above), this witness-class document must be
updated before repair enumeration begins, because the paper's flagship claim may
need to be weakened.

### Step 0 implementation constraint (recorded from the first prototype)

The exploratory Step 0 checker lives at
`scripts/exploration/candidate_b/step0_equiv_check.py` (see its README). Its
first run records a generator-interface constraint that currently blocks
family-scale ≡CM measurement:

- the split levers `decisive_voter0` / `decisive_voter1` are encoded only in the
  legacy `selectors_v1` MINLIB mode, which `encoding/schema.py` restricts to the
  Sen24 base case `(2,4)`; outside `(2,4)` the parametric `pair_selectors_v1`
  mode is used and the split levers are not defined;
- consequently, at `(2,5)` and `(3,4)` the bundled package generates but the
  transport-map split image cannot be generated, so both cases are classified
  `inconclusive` (≡CM not evaluable), while the `(2,4)` base-case control
  classifies `equiv_cm_persists` and validates the ρ-construction machinery.

A family-scale parametric split encoding of the liberalism layer (a per-voter
analogue of `decisive_voter*` valid under `pair_selectors_v1`) is therefore a
prerequisite for measuring ≡CM persistence, and its design is part of the Step 0
review. The fixed two-lever split image may additionally be structurally
insufficient where the voter count exceeds two (e.g. `(3,4)`), which is itself a
finding about the transport map's scope rather than a checker fault.

---

## Required new artifacts

The M2.1 witness class requires the following new artifacts. None exist yet; this
list scopes what the reviewed prototype is allowed to produce. The Step-0
equivalence report comes first; the later artifacts are authorized only after
Step 0 has been reviewed.

1. **Step-0 equivalence report.** The first required artifact. For each case
   `(2,5)` and `(3,4)` it records:
   - bundled/split generated package identifiers,
   - variable counts,
   - clause counts,
   - clause-multiset comparison result (the ≡CM classification above),
   - satisfiability-status comparison result,
   - the mapping `π` used,
   - a scope statement distinguishing local-rationality
     (`no_cycle3 ∧ no_cycle4`) from full `SocialAcyclic`.
2. **Bundled/split family-scale encodings.** Bundled and split CNFs (or
   equivalent encodings) generated at `(2,5)` and `(3,4)`.
3. **Repair enumeration outputs.** Inclusion-minimal repair (MCS) enumerations
   for each bundled and split package at each larger case.
4. **Transport map.** An explicit, machine-readable record of the
   repair-transport map `π` (with `π(minlib) = {decisive_voter0, decisive_voter1}`
   and singleton images for the shared levers) at each case, used to align
   bundled and split repairs.
5. **Repair comparison report.** A report that pairs bundled and split repair
   sets under `π` and classifies each pair as canonical-preserving or
   non-canonical at family scale.
6. **Scope statement.** A statement distinguishing local-rationality
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
