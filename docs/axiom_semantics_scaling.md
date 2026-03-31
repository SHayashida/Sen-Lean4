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
as instances of the **same axiom schema** across cases (2,4), (2,5), and (3,4).
Observed non-liftability must be attributable to genuine repair structure change,
not to semantic drift in the encoding.

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
**fixed to n=2, m=4**. The confirmation below cannot be completed until a parametric
schema and parametric auditor are implemented.

Do not attempt to sign off this memo using the current `sen24`-fixed tools.

---

## Lever-by-Lever Analysis

### `asymm` — Asymmetry

**Schema:** ∀i, ∀x≠y: xPᵢy → ¬yPᵢx

**Scaling:** Clause count scales as n·m(m−1)/2. Schema is structurally unchanged.  
**Risk:** Low.

| Check | Current status | After generalization |
|---|---|---|
| Same logical form across cases | ☐ unverified | ☐ to confirm |
| CNF clause structure invariant | ☐ unverified | ☐ to confirm |

---

### `un` — Unanimity (Pareto)

**⚠️ Correction from v0.1:** This lever is **Unanimity / Pareto**, not Universal Domain.
Universal Domain is a background assumption of the encoding (all profiles are admitted),
not a separate axiom lever. Treating `un` as Universal Domain is a category error that
would cause the entire schema confirmation to target the wrong axiom.

**Schema:** ∀x,y: (∀i: xPᵢy) → xPy

**Scaling:** Quantifies over all voter–alternative combinations.
Schema is structurally unchanged; clause count scales with n and m(m−1)/2.  
**Risk:** Low, but must confirm quantifier structure is not hard-coded to n=2.

| Check | Current status | After generalization |
|---|---|---|
| Correctly identified as Pareto, not Universal Domain | ✓ confirmed in this memo | ✓ |
| Quantifier structure not hard-coded to n=2 | ☐ unverified | ☐ to confirm |
| Clause count scales correctly with n,m | ☐ unverified | ☐ to confirm |

---

### `minlib` — Minimal Liberalism

**⚠️ Strong blocker — not a light check.**

**Schema:** ∃ at least two distinct individuals i≠j, each decisive over at least one pair.  
Decisive(i,x,y) := (xPᵢy → xPy) ∧ (yPᵢx → yPx)

**Why this is a strong blocker:**

Moving to n=3 changes:
- How selectors are represented (which individual holds which decisive pair)
- The existential structure (must ensure ≥2 distinct decisive individuals among 3)
- Voter index handling: if individual indices are hard-coded, the schema breaks at n=3

The current encoder was designed for n=2. At n=3, the existential quantification
over individuals must be verified not to collapse into n=2 semantics or to inadvertently
require all 3 individuals to be decisive.

**Status: Cannot be confirmed without generalized encoder.**

| Check | Current status | After generalization |
|---|---|---|
| Existential quantification over individuals is parametric | ☐ BLOCKED | ☐ to confirm |
| No hard-coded individual indices | ☐ BLOCKED | ☐ to confirm |
| Decisiveness structure correct at n=3 | ☐ BLOCKED | ☐ to confirm |

---

### `no_cycle3` — Acyclicity (length 3)

**Schema:** ∀x,y,z distinct: ¬(xPy ∧ yPz ∧ zPx)

**Coverage by case:**

| Case | # triples C(m,3) |
|---|---|
| (2,4) | 4 |
| (2,5) | 10 |
| (3,4) | 4 |

The logical form is the same instance schema. However, at m=5, `no_cycle3 ∧ no_cycle4`
still permits length-5 cycles. The effective acyclicity constraint is qualitatively
weaker at m=5 than at m=4.

**Key judgment required before sign-off:** If non-liftability is observed at (2,5),
is it because repair structure genuinely changed, or because `no_cycle3/4` permits
longer cycles that were absent at m=4? This confound must be explicitly resolved.

| Check | Current status | After generalization |
|---|---|---|
| Same logical form across cases | ☐ unverified | ☐ to confirm |
| Effective-strength confound assessed | ☐ unverified | ☐ judgment required |

*Notes (fill after analysis):*
> [To be completed]

---

### `no_cycle4` — Acyclicity (length 4)

**Schema:** ∀x,y,z,w distinct: ¬(xPy ∧ yPz ∧ zPw ∧ wPx)

**Coverage by case:**

| Case | # 4-tuples C(m,4) |
|---|---|
| (2,4) | 1 |
| (2,5) | 5 |
| (3,4) | 1 |

Same structural situation as `no_cycle3`. At m=5, five 4-cycles must be prohibited
versus one at m=4. The schema is the same instance form, but coverage differs.

| Check | Current status | After generalization |
|---|---|---|
| Same logical form across cases | ☐ unverified | ☐ to confirm |
| Effective-strength confound assessed | ☐ unverified | ☐ judgment required |

*Notes (fill after analysis):*
> [To be completed]

---

## Combined Status Table

| Lever | Schema uniform? | Effective strength change? | Blocker level |
|---|---|---|---|
| `asymm` | ☐ | Low | Weak |
| `un` (= Pareto) | ☐ | Low | Weak |
| `minlib` | ☐ | **High at n=3** | **Strong blocker** |
| `no_cycle3` | ☐ | Medium at m=5 | Moderate — judgment required |
| `no_cycle4` | ☐ | Medium at m=5 | Moderate — judgment required |

---

## Decision Gate

**Proceed with experiment only if:**

1. Parametric encoder and auditor implemented (`docs/schema_generalization_design.md`)
2. All schema-uniformity checks verified against generalized implementation
3. `minlib` existential structure confirmed correct at n=3
4. `no_cycle3/4` effective-strength confound explicitly judged not to invalidate results
5. All sign-off checkboxes below are checked

**Do not proceed if:**
- `minlib` existential structure is unverified at n=3
- `no_cycle3/4` confound is unresolved and a non-liftability result is observed
  (result would be ambiguous and unusable as Candidate A evidence)

---

## Sign-off (complete only after generalized implementation)

- [ ] `asymm`: schema confirmed uniform, clause structure verified
- [ ] `un` (Pareto): schema confirmed uniform, not confused with Universal Domain
- [ ] `minlib`: existential structure verified at n=3, no hard-coded indices
- [ ] `no_cycle3`: schema uniform; effective-strength confound assessed and resolved
- [ ] `no_cycle4`: schema uniform; effective-strength confound assessed and resolved
- [ ] Generalized auditor produces clean audit for all three cases
- [ ] Experiment cleared to run
