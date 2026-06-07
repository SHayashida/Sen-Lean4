# Candidate B: Parametric Split Liberalism Encoding — Design Options (M2.1)
## Choosing a family-scale split encoding without destroying the ≡CM blade

**Milestone:** M2.1
**Branch intent:** `codex/m2.1-candidate-b`
**Status:** Design memo (doc-only; no encoder, generator, or repair enumeration).
**Related:** [docs/candidate_b_encoding_sensitivity.md](candidate_b_encoding_sensitivity.md),
[docs/candidate_b_minlib_granularity.md](candidate_b_minlib_granularity.md),
[docs/m2_scope_wall.md](m2_scope_wall.md),
[docs/no_cycle_interpretation_note.md](no_cycle_interpretation_note.md),
[scripts/exploration/candidate_b/README.md](../scripts/exploration/candidate_b/README.md)

This document designs and compares candidate family-scale split liberalism
encodings **before** any generator is changed. The central constraint is that the
M1.5 clause-multiset-equivalence (≡CM) blade must be protected: no option may be
adopted before a feasibility check shows whether it preserves ≡CM.

---

## 1. Background

The M2.1 Step 0 checker
(`scripts/exploration/candidate_b/step0_equiv_check.py`) produced:

- **(2,4) base-case control:** `equiv_cm_persists` — an identity variable-renaming
  bijection ρ was constructed and re-verified, and SAT/UNSAT status agrees
  (UNSAT/UNSAT). This validates the ρ-construction machinery against the known
  M1.5 result.
- **(2,5):** `inconclusive`, because the split package is not generable.
- **(3,4):** `inconclusive`, because the split package is not generable.

Root cause: the split levers `decisive_voter0` / `decisive_voter1` are encoded
only in the legacy `selectors_v1` MINLIB mode, which `encoding/schema.py`
restricts to the Sen24 base case `(2,4)`. Outside `(2,4)` the parametric
`pair_selectors_v1` mode is used, in which the split levers are undefined; the
bundled package still generates, but the transport-map split image cannot.

Three statements must be read together:

- **Step 0 did not fail.** It executed correctly and produced reviewed,
  reproducible classifications.
- **Step 0 discovered that the M1.5 split witness class is not yet defined at
  family scale.** The missing object is a family-scale split liberalism encoding;
  this is a design gap, not a checker fault.
- **Repair enumeration remains unauthorized.** No MCS or repair enumeration has
  started, and none may start until the gates in Section 8 are satisfied.

---

## 2. Design problem

The missing object is:

> a family-scale split liberalism encoding comparable to bundled `minlib`.

It must expose the liberalism layer through person-specific (or witness-specific)
decisive levers at cases beyond `(2,4)`, so that bundled `minlib` and its split
image can be compared lever-by-lever under the repair-transport map π.

Why this matters for M2.1:

- M2.1 cannot test repair-candidate representation non-canonicity at family scale
  until this split encoding exists. Without it, every family-scale case is
  `inconclusive` by generation, as Step 0 shows.
- **The key requirement is not merely satisfiability-equivalence.** Two encodings
  can share SAT/UNSAT status while differing in clause structure; that alone does
  not protect the M1.5 argument.
- **The strongest M1.5-style claim requires clause-multiset equivalence (≡CM)**
  under a documented variable/lever correspondence ρ: the bundled and split
  clause multisets must coincide up to a verified variable renaming.
- **If ≡CM fails, any observed repair divergence may be explainable by
  encoding-strength or selector-logic differences** rather than by
  representation granularity alone. The M1.5 blade is precisely that ≡CM rules
  those alternative explanations out; losing ≡CM blunts the blade.

The design task is therefore to find a split encoding that is generable at family
scale **and** plausibly ≡CM-preserving relative to bundled `minlib`.

---

## 3. Candidate designs

The bundled reference package throughout is
`asymm + un + minlib + no_cycle3 + no_cycle4`, and π maps `minlib` to a split
image while carrying every shared lever to its singleton counterpart.

### Option A — two-witness split

`minlib` maps to two selected decisive-witness levers (the direct generalization
of the Sen24 base-case split `{decisive_voter0, decisive_voter1}`).

- **Relation to the M1.5 base-case split:** closest of all options; at `(2,4)` it
  is exactly the M1.5 split.
- **Behavior at (2,5):** plausible — two voters, varying alternatives; the two
  witnesses remain the two voters, and only the alternative dimension grows. The
  open question is whether the parametric encoder reproduces the legacy clause
  layout closely enough for ≡CM.
- **Behavior at (3,4):** ambiguous — with three voters, "two selected witnesses"
  must choose *which* two, which reintroduces a selection question (see Option C).
- **≡CM likelihood:** high at `(2,m)`; uncertain at `n > 2`.
- **Selector variables/clauses:** none if the two witnesses are fixed (no
  choice); selection logic appears only once a choice among more than two voters
  is required.
- **MINLIB-meaning risk:** low while the witnesses are the actual voters and not a
  re-interpretation of the liberalism requirement.
- **Keeps M2.1 focused:** yes at `(2,m)`; at `n > 2` it collapses into Option C's
  selection problem.

Option A is best understood as the `(2,m)` case of the family (then it coincides
with Option D) plus an unresolved `n > 2` selection question (then it coincides
with Option C).

### Option B — all-voter split

`minlib` maps to all voter-specific decisive levers
`{decisive_voter0, ..., decisive_voter(n-1)}`.

- **Relation to the M1.5 base-case split:** at `(2,4)` it equals the M1.5 split
  (two voters), but for `n > 2` it adds one decisive lever per additional voter.
- **Behavior at (2,5):** identical to Option A/D (only two voters exist).
- **Behavior at (3,4):** introduces a third decisive lever with no bundled
  counterpart, so the bundled→split correspondence is no longer one bundled lever
  to a fixed-size image.
- **≡CM likelihood:** low at `n > 2` — the extra per-voter levers add clauses with
  no bundled match, so a verified ρ is unlikely to exist.
- **Selector variables/clauses:** not selector clauses per se, but additional
  decisive-lever clauses that are unmatched on the bundled side.
- **MINLIB-meaning risk:** **high.** Exposing *all* voters as independent decisive
  levers changes the liberalism layer's content (it strengthens/redefines the
  minimal-liberalism requirement into per-voter decisiveness), rather than merely
  changing representation granularity.
- **Keeps M2.1 focused:** no — it risks turning M2.1 into an all-voter liberalism
  redesign.

### Option C — pair-selector split

`minlib` maps to the two sides of a *selected* existential witness pair:
`π(minlib) = {selected_decisive_left, selected_decisive_right}`.

- **Relation to the M1.5 base-case split:** at `(2,4)` the selected pair is the
  only pair, so it reduces to the M1.5 split; beyond `(2,4)` it generalizes by
  selecting a witness pair rather than fixing voters 0 and 1.
- **Behavior at (2,5):** workable but heavier than Option D — the selection is
  trivial (still two voters) yet the pair-selector machinery is present.
- **Behavior at (3,4):** this is the option's intended use — it lets the
  liberalism witness be chosen among more than two voters, so it is attractive
  for `n > 2`.
- **≡CM likelihood:** **uncertain and at risk.** This is the deputy concern:
  choosing the witness pair generally requires **selector variables and selector
  clauses** (existential at-least-one / at-most-one and selector→content
  implications). Those clauses live on the split side and have no bundled
  counterpart, so they are likely to be *unmatched* under any ρ, breaking ≡CM.
- **Selector variables/clauses:** yes, by construction — this is the defining
  feature of the option and the source of the ≡CM risk.
- **MINLIB-meaning risk:** moderate — selection is existential, matching the
  intended "there exists a decisive witness" reading, but the added selector
  logic is extra machinery beyond the bundled representation.
- **Keeps M2.1 focused:** conditionally — only if the selector clauses do not
  destroy the ≡CM comparison or if a weakened (satisfiability-equivalence) claim
  is explicitly accepted.

**Do not claim Option C is best until feasibility is checked.** Its `n > 2` reach
is the most valuable property, but its selector machinery is exactly what could
remove the M1.5 blade.

### Option D — `(2,m)`-restricted two-witness split

Restrict the first M2.1 target family to two voters and varying alternatives,
starting with `(2,5)`. Keep the two witness voters fixed
(`decisive_voter0`, `decisive_voter1`), avoiding all voter-selector logic, and
generalize only the alternative dimension first.

- **Relation to the M1.5 base-case split:** the direct, minimal generalization —
  same two fixed witnesses as `(2,4)`, only `m` grows.
- **Behavior at (2,5):** the primary target; two fixed witnesses, five
  alternatives, no selection logic.
- **Behavior at (3,4):** explicitly out of scope for this option — `(3,4)` is
  deferred to a later extension or an M2.2/future-work path unless Option C proves
  ≡CM-feasible.
- **≡CM likelihood:** **highest** of all options — no selector clauses are
  introduced, so the only question is whether the parametric alternative-dimension
  encoding admits a verified ρ against bundled `minlib`.
- **Selector variables/clauses:** none.
- **MINLIB-meaning risk:** lowest — the liberalism layer keeps two fixed decisive
  witnesses, so only representation granularity changes.
- **Keeps M2.1 focused:** yes — it keeps M2.1 a repair-candidate representation
  transfer study rather than a liberalism redesign.

Option D is the most conservative path for preserving the M1.5 ≡CM blade.

---

## 4. Provisional recommendation

**Do not immediately adopt Option C.** The recommended decision rule is:

- **Primary path — Option D.** Start with the `(2,m)`-restricted two-witness
  split. If it can generate bundled/split packages for `(2,5)` and preserve, or
  plausibly preserve, ≡CM, it best protects the M1.5 clause-multiset-equivalence
  argument and yields the first strong M2.1 claim at `(2,5)`.
- **Secondary path — Option C.** Investigate the pair-selector split only as a
  feasibility branch for `n > 2`. Option C may become the correct design for
  `(3,4)`, but only if its selector machinery does not destroy the intended
  comparison, or if a weakened (satisfiability-equivalence) claim is explicitly
  accepted.
- **Deferred path — Option B.** The all-voter split should not be the default,
  because it risks turning M2.1 into an all-voter liberalism redesign rather than
  a repair-representation transfer study. (Option A is subsumed: it equals
  Option D at `(2,m)` and reduces to Option C at `n > 2`.)

---

## 5. Feasibility-first policy

**No option is adopted until a minimal feasibility check is performed.** The
feasibility check must answer, for the candidate design and target case:

1. Can the bundled package be generated?
2. Can the split package be generated?
3. Do variable counts and clause counts make ≡CM *plausible*? (Counts are
   necessary, never sufficient.)
4. Can a variable-renaming map ρ be constructed and verified?
5. Does SAT/UNSAT status agree?
6. Are any new selector clauses introduced **only on the split side**?
7. If selector clauses are introduced, can the bundled side be made
   clause-multiset comparable **without changing the meaning of the bundled
   representation**?

Explicit consequences:

- **If Option C introduces unmatched selector clauses, then Option C cannot
  support the strong M1.5-style ≡CM claim.** In that case, exactly one of:
  1. **M2.1 narrows to Option D / `(2,m)` first**, taking the strong claim there
     and deferring `n > 2`; or
  2. **M2.1 weakens its claim** to satisfiability-equivalent representation
     divergence, explicitly noting that the ≡CM shield no longer rules out
     logical-strength or selector-logic explanations; or
  3. **the failure of ≡CM persistence becomes a negative result** about the
     boundary of the M1.5 witness class (an encoding-transfer boundary finding).

The feasibility check itself reuses the existing Step 0 checker; it adds no new
encoder and authorizes no repair enumeration.

---

## 6. Transport maps

The transport maps below are stated as lever correspondences using set-valued
images, deliberately avoiding logical symbols. **π is a lever correspondence /
repair-transport map, not a semantic equivalence claim** between axiom formulas.

### Option D / two-voter restricted path

```
π(minlib)    = {decisive_voter0, decisive_voter1}
π(asymm)     = {asymm}
π(un)        = {un}
π(no_cycle3) = {no_cycle3}
π(no_cycle4) = {no_cycle4}
```

### Option C / pair-selector path

```
π(minlib)    = {selected_decisive_left, selected_decisive_right}
π(asymm)     = {asymm}
π(un)        = {un}
π(no_cycle3) = {no_cycle3}
π(no_cycle4) = {no_cycle4}
```

In both maps, every shared lever maps to its singleton counterpart; only the
liberalism lever `minlib` has a two-element split image.

---

## 7. Step 0 rerun plan

After a candidate split design is implemented, the Step 0 checker
(`scripts/exploration/candidate_b/step0_equiv_check.py`) must be rerun and the
classifications reviewed before any further step.

- **For Option D**, rerun on:
  - `(2,4)` — base-case control,
  - `(2,5)` — first M2.1 target.

  Do **not** require `(3,4)` for the first strong M2.1 claim.

- **For Option C**, rerun on:
  - `(2,4)` — base-case control,
  - `(2,5)`,
  - `(3,4)`.

The classifications remain the existing Step 0 vocabulary:

- `equiv_cm_persists`
- `sat_equiv_only`
- `status_diverges`
- `inconclusive`

---

## 8. Gates before repair enumeration

Repair enumeration remains **unauthorized** until all of the following hold:

- this design document is reviewed;
- a candidate split design is selected;
- split package generation succeeds for the selected target cases;
- the Step 0 rerun has a reviewed classification;
- if ≡CM fails, the M2.1 claim is explicitly revised (per Section 5) **before**
  repair enumeration begins.

---

## 9. Scope discipline

- This work is **local-rationality only.**
- `no_cycle3 ∧ no_cycle4` is **not** full `SocialAcyclic` at family scale.
- This does **not** alter M2.
- This does **not** claim the sen24 CNF is a family-level certificate.
- This does **not** touch `sen_impossibility_lifts` or any M2 theorem statement,
  M2 paper claim, or baseline CNF/LRAT certificate.
- M2 = transfer of the legitimization / impossibility guarantee. M2.1 = transfer
  of repair-candidate representation non-canonicity. M2.1 is not
  status/impossibility transfer.
