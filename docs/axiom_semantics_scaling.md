# Axiom Semantics Scaling Memo
## Prerequisite for Repair Liftability Experiment

**Status:** INCOMPLETE — sign-off not yet possible  
**Blocker:** Repository is currently `sen24`-fixed. Parametric schema/auditor must be
implemented before this memo can be completed.  
**See:** `docs/schema_generalization_design.md` for the required implementation step.  
**Location:** `docs/axiom_semantics_scaling.md`

---

## Purpose

Confirm that all axiom levers used in the repair liftability experiment are interpreted
as instances of the **same axiom schema** across cases `(2,4)`, `(2,5)`, and `(3,4)`.

Observed non-liftability must be attributable to genuine repair-structure change,
not to semantic drift in the encoding.

This memo therefore separates two questions that must not be conflated:

1. **Schema uniformity:** Is the same logical schema being instantiated at different sizes?
2. **Experimental usability:** Even if the schema is uniform, is the lever still safe to use
   as evidence for **Candidate A** (repair non-liftability), or does effective-strength drift
   make the result ambiguous?

---

## Cases Under Examination

| Case | n (voters) | m (alternatives) |
|---|---|---|
| Base | 2 | 4 |
| Larger-1 | 2 | 5 |
| Larger-2 | 3 | 4 |

---

## Current Repository Limitation

The existing codebase (`gen_sen24_dimacs.py`, `check_sen24_cnf.py`, `schema.py`) is
**fixed to `n=2, m=4`**. The confirmation below cannot be completed until a parametric
schema and parametric auditor are implemented.

Do **not** attempt to sign off this memo using the current `sen24`-fixed tools.

---

## Lever-by-Lever Analysis

### `asymm` — Asymmetry

**Lean-side target schema**  
The social strict relation should be asymmetric.

**CNF-side finite instance pattern**  
For each profile `p` and each ordered pair of distinct alternatives `(a,b)`:

- `¬P_p(a,b) ∨ ¬P_p(b,a)`

where `P_p(a,b)` is the social strict preference variable at profile `p`.

**Scaling**  
The clause family is structurally unchanged.
Only the number of instantiated profiles and ordered pairs changes.

**Risk**  
Low.

| Check | Current status | After generalization |
|---|---|---|
| Lean-side target identified correctly | ✓ | ✓ |
| Same CNF-side logical pattern across cases | ☐ unverified | ☐ to confirm |
| Clause family remains profile-local social asymmetry | ☐ unverified | ☐ to confirm |

---

### `un` — Unanimity (Pareto)

**⚠️ Correction from earlier drafts**  
This lever is **Unanimity / Pareto**, **not** Universal Domain.

Universal Domain is a background assumption of the encoding
(all profiles are admitted), not a separate axiom lever.
Treating `un` as Universal Domain would target the wrong axiom entirely.

**Lean-side target schema**  
If all voters prefer `x` to `y`, then the social relation ranks `x` above `y`.

**CNF-side finite instance pattern**  
For each profile `p` and ordered pair `(a,b)`:

- if all voters in `p` strictly prefer `a` to `b`,
- then require the social relation at `p` to contain `a > b`.

Representative clause pattern:

- `¬AllPrefer_p(a,b) ∨ P_p(a,b)`

where `AllPrefer_p(a,b)` abbreviates the all-voter antecedent at profile `p`.

**Scaling**  
The schema is structurally unchanged if the encoder truly quantifies over **all** voters.
The main risk is accidental hard-coding to exactly two voter positions.

**Risk**  
Low to moderate until quantifier structure is confirmed parametric.

| Check | Current status | After generalization |
|---|---|---|
| Correctly identified as Pareto, not Universal Domain | ✓ confirmed in this memo | ✓ |
| Lean-side target identified correctly | ✓ | ✓ |
| All-voter quantification not hard-coded to `n=2` | ☐ unverified | ☐ to confirm |
| Same CNF-side implication pattern across cases | ☐ unverified | ☐ to confirm |

---

### `minlib` — Minimal Liberalism

**⚠️ Strong blocker — not a light check.**

**Lean-side target schema**  
There exist at least two distinct individuals `i ≠ j`, each decisive over at least one pair.

**CNF-side finite instance pattern**  
The finite encoder must represent:

- two **distinct** decisive individuals,
- each with at least one decisive pair witness,
- without relying on fixed voter identities such as “voter 0” and “voter 1”.

Representative decisiveness meaning:

- `Decisive(i,a,b)` means that individual `i` controls the social ranking of pair `(a,b)`.

**Why this is a strong blocker**

Moving to `n=3` changes:

- how selectors are represented,
- the existential structure over individuals,
- how distinctness of decisive individuals is enforced,
- whether voter indices are hard-coded.

If the current encoding is still effectively tied to two named voters,
then the schema is **not** yet confirmed across `(2,4)`, `(2,5)`, `(3,4)`.

**Status**  
Cannot be confirmed without generalized encoder.

| Check | Current status | After generalization |
|---|---|---|
| Lean-side target identified correctly | ✓ | ✓ |
| Existential quantification over individuals is parametric | ☐ BLOCKED | ☐ to confirm |
| No hard-coded individual indices | ☐ BLOCKED | ☐ to confirm |
| Distinctness of two decisive individuals preserved at `n=3` | ☐ BLOCKED | ☐ to confirm |
| CNF-side witness structure is uniform across cases | ☐ BLOCKED | ☐ to confirm |

---

### `no_cycle3` — Local 3-cycle Prohibition

**Lean-side target schema**  
This lever is **not** full `SocialAcyclic`.
It is a finite local approximation to rationality / acyclicity.

**CNF-side finite instance pattern**  
For each profile `p` and each triple of distinct alternatives `(a,b,c)`:

- `¬(P_p(a,b) ∧ P_p(b,c) ∧ P_p(c,a))`

equivalently as a clause:

- `¬P_p(a,b) ∨ ¬P_p(b,c) ∨ ¬P_p(c,a)`

**Coverage by case**

| Case | # triples `C(m,3)` |
|---|---|
| (2,4) | 4 |
| (2,5) | 10 |
| (3,4) | 4 |

**Scaling / confound**  
The local clause pattern is the same, but at `m=5`, `no_cycle3 ∧ no_cycle4`
still permits length-5 cycles. Thus the effective rationality constraint is weaker,
relative to full acyclicity, at `m=5` than at `m=4`.

**Key question for Candidate A**  
If non-liftability is observed at `(2,5)`, is it due to genuine repair-structure change,
or because longer cycles are newly available?

**Risk**  
Moderate.

| Check | Current status | After generalization |
|---|---|---|
| Lean-side role correctly identified as local approximation, not full acyclicity | ✓ | ✓ |
| Same local CNF clause pattern across cases | ☐ unverified | ☐ to confirm |
| Effective-strength confound assessed | ☐ unverified | ☐ judgment required |
| Candidate A usability judged explicitly | ☐ unverified | ☐ judgment required |

*Notes (fill after analysis):*
> [To be completed]

---

### `no_cycle4` — Local 4-cycle Prohibition

**Lean-side target schema**  
As with `no_cycle3`, this lever is a local finite approximation, not full `SocialAcyclic`.

**CNF-side finite instance pattern**  
For each profile `p` and each 4-tuple of distinct alternatives `(a,b,c,d)`:

- `¬(P_p(a,b) ∧ P_p(b,c) ∧ P_p(c,d) ∧ P_p(d,a))`

equivalently:

- `¬P_p(a,b) ∨ ¬P_p(b,c) ∨ ¬P_p(c,d) ∨ ¬P_p(d,a)`

**Coverage by case**

| Case | # 4-tuples `C(m,4)` |
|---|---|
| (2,4) | 1 |
| (2,5) | 5 |
| (3,4) | 1 |

**Scaling / confound**  
The local clause pattern is the same, but coverage changes materially with `m`.
At `m=5`, five distinct 4-cycles must be ruled out, and even then 5-cycles remain possible.

**Risk**  
Moderate.

| Check | Current status | After generalization |
|---|---|---|
| Lean-side role correctly identified as local approximation, not full acyclicity | ✓ | ✓ |
| Same local CNF clause pattern across cases | ☐ unverified | ☐ to confirm |
| Effective-strength confound assessed | ☐ unverified | ☐ judgment required |
| Candidate A usability judged explicitly | ☐ unverified | ☐ judgment required |

*Notes (fill after analysis):*
> [To be completed]

---

## Combined Status Table

| Lever | Schema uniform? | Effective-strength confound? | Candidate A usable? | Blocker level |
|---|---|---|---|---|
| `asymm` | ☐ | Low | Likely yes | Weak |
| `un` (= Pareto) | ☐ | Low | Likely yes | Weak |
| `minlib` | ☐ | High at `n=3` | No, until generalized | **Strong blocker** |
| `no_cycle3` | ☐ | Medium at `m=5` | Judgment required | Moderate |
| `no_cycle4` | ☐ | Medium at `m=5` | Judgment required | Moderate |

---

## Decision Gate

**Proceed with experiment only if:**

1. Parametric encoder and auditor implemented (`docs/schema_generalization_design.md`)
2. All schema-uniformity checks verified against generalized implementation
3. `minlib` existential structure confirmed correct at `n=3`
4. `no_cycle3/4` effective-strength confound explicitly resolved by either:
   - a **stronger rationality encoding**, or
   - an **explicit restriction of claim scope**
5. All sign-off checkboxes below are checked

**Do not proceed if:**
- `minlib` existential structure is unverified at `n=3`
- `no_cycle3/4` confound is unresolved and a non-liftability result is observed
  (the result would be ambiguous and unusable as Candidate A evidence)

---

## Sign-off (complete only after generalized implementation)

- [ ] `asymm`: Lean target and CNF pattern confirmed uniform
- [ ] `un` (Pareto): correctly identified; CNF pattern confirmed uniform
- [ ] `minlib`: existential structure verified at `n=3`, no hard-coded indices
- [ ] `no_cycle3`: local schema uniform; confound assessed; Candidate A usability decided
- [ ] `no_cycle4`: local schema uniform; confound assessed; Candidate A usability decided
- [ ] Generalized auditor produces clean audit for all three cases
- [ ] Experiment cleared to run