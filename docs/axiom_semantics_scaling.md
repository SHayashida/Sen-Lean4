# Axiom Semantics Scaling Memo
## Prerequisite for Repair Liftability Experiment

**Status:** INCOMPLETE — schema-uniformity evidence is now in place, but final sign-off is still not possible.  
**Remaining blocker:** Step 0 is implemented; sign-off is still blocked on the effective-strength and claim-scope judgment for `no_cycle3` and `no_cycle4`.  
**See:** `docs/schema_generalization_design.md` and `docs/schema_generalization_tasklist.md`.  
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

## Current Repository State

The Step 0 prerequisite is now implemented:

- `encoding/schema.py` provides `FiniteSchema(n, m, minlib_mode=...)`.
- `scripts/gen_dimacs.py` now emits parametric CNFs for `(2,4)`, `(2,5)`, and `(3,4)`.
- `scripts/check_parametric_cnf.py` audits the generalized schema family.
- `scripts/check_sen24_cnf.py` remains the exact baseline auditor for the committed Sen24 artifact.

Do **not** treat this as experiment sign-off yet. The remaining open question is not schema generation,
but whether `no_cycle3` and `no_cycle4` are acceptable as Candidate A evidence once `m=5` allows longer cycles.

---

## Evidence Snapshot

Schema-uniformity evidence has been generated and audited for:

| Case | Encoding | `minlib` mode | `nvars` | `nclauses` |
|---|---|---|---:|---:|
| `(2,4)` generalized base-size run | `finite_schema_v1` | `pair_selectors_v1` | 6937 | 50115 |
| `(2,5)` | `finite_schema_v1` | `pair_selectors_v1` | 288041 | 3528003 |
| `(3,4)` | `finite_schema_v1` | `pair_selectors_v1` | 165927 | 1347847 |

The exact commands, category counts, and CNF hashes are recorded in `docs/schema_generalization_tasklist.md`.

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
| Same CNF-side logical pattern across cases | ✓ confirmed by `check_parametric_cnf.py` | ✓ |
| Clause family remains profile-local social asymmetry | ✓ confirmed by audited runs | ✓ |

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
| All-voter quantification not hard-coded to `n=2` | ✓ confirmed via `FiniteSchema.all_voters_prefer` and audited `(3,4)` run | ✓ |
| Same CNF-side implication pattern across cases | ✓ confirmed by audited runs | ✓ |

---

### `minlib` — Minimal Liberalism

**⚠️ Step 0 blocker resolved in code, but still worth treating as a sensitive lever.**

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

The repository now uses a parametric witness structure for generalized runs:

- one selector per unordered pair of distinct voters,
- one decisive-witness variable per `(voter, ordered pair)`,
- two support clauses per selected voter pair, and
- profile-local decisiveness implications for each decisive witness.

This removes fixed names such as `pref0/pref1` or `sel0/sel1` from the generalized path.
The legacy Sen24 selector layout remains available only as a compatibility mode for the committed `(2,4)` artifact.

| Check | Current status | After generalization |
|---|---|---|
| Lean-side target identified correctly | ✓ | ✓ |
| Existential quantification over individuals is parametric | ✓ confirmed by `pair_selectors_v1` | ✓ |
| No hard-coded individual indices | ✓ confirmed on generalized path | ✓ |
| Distinctness of two decisive individuals preserved at `n=3` | ✓ confirmed via unordered voter-pair selectors on `(3,4)` | ✓ |
| CNF-side witness structure is uniform across cases | ✓ confirmed for generalized `(2,4)`, `(2,5)`, `(3,4)` runs | ✓ |

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
| Same local CNF clause pattern across cases | ✓ confirmed by audited runs | ✓ |
| Effective-strength confound assessed | ✓ documented; still not resolved for sign-off | ☐ judgment required |
| Candidate A usability judged explicitly | ☐ still open | ☐ judgment required |

*Notes:*
> Step 0 confirms schema uniformity only. At `m=5`, the local short-cycle ban still allows 5-cycles, so the later interpretive judgment remains separate.

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
| Same local CNF clause pattern across cases | ✓ confirmed by audited runs | ✓ |
| Effective-strength confound assessed | ✓ documented; still not resolved for sign-off | ☐ judgment required |
| Candidate A usability judged explicitly | ☐ still open | ☐ judgment required |

*Notes:*
> Step 0 confirms schema uniformity only. At `m=5`, banning all 4-cycles still does not imply full acyclicity because 5-cycles remain available.

---

## Combined Status Table

| Lever | Schema uniform? | Effective-strength confound? | Candidate A usable? | Blocker level |
|---|---|---|---|---|
| `asymm` | ✓ | Low | Likely yes | Weak |
| `un` (= Pareto) | ✓ | Low | Likely yes | Weak |
| `minlib` | ✓ | Low for schema uniformity; still a sensitive lever semantically | Yes for Step 0 | Resolved for Step 0 |
| `no_cycle3` | ✓ | Medium at `m=5` | Judgment required | Moderate |
| `no_cycle4` | ✓ | Medium at `m=5` | Judgment required | Moderate |

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

- [x] `asymm`: Lean target and CNF pattern confirmed uniform
- [x] `un` (Pareto): correctly identified; CNF pattern confirmed uniform
- [x] `minlib`: existential structure verified at `n=3`, no hard-coded indices
- [ ] `no_cycle3`: local schema uniform; confound assessed; Candidate A usability decided
- [ ] `no_cycle4`: local schema uniform; confound assessed; Candidate A usability decided
- [x] Generalized auditor produces clean audit for all three cases
- [ ] Experiment cleared to run
