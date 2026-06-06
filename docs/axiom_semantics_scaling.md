# Axiom Semantics Scaling Memo
## Step 0.5 Sign-off for Repair Liftability Experiment

**Status:** COMPLETE under explicit restricted scope.  
**Resolution policy:** `no_cycle3` and `no_cycle4` are treated as local forbidden-pattern approximations, not as full acyclicity.  
**Experiment status:** Cleared to run under that restricted interpretation.  
**See:** `docs/schema_generalization_tasklist.md` and `docs/no_cycle_interpretation_note.md`.  
**Location:** `docs/axiom_semantics_scaling.md`

---

## Purpose

Confirm that all five levers used in the repair liftability experiment are interpreted
as instances of the same axiom schema across cases `(2,4)`, `(2,5)`, and `(3,4)`.

This memo separates two questions:

1. **Schema uniformity:** is the same logical clause family instantiated at different finite sizes?
2. **Interpretive scope:** even if the schema is uniform, what claim scope is legitimate when effective strength changes with `m`?

Step 0 already resolved the first question by implementing a parametric schema and a parametric auditor.
Step 0.5 resolves the second question by restricting claim scope rather than changing the encoding.

---

## Cases Under Examination

| Case | n (voters) | m (alternatives) |
|---|---|---|
| Base | 2 | 4 |
| Larger-1 | 2 | 5 |
| Larger-2 | 3 | 4 |

---

## Step 0 Evidence

Step 0 established:

- a parametric `FiniteSchema(n, m, minlib_mode=...)`,
- generalized generation for `(2,4)`, `(2,5)`, and `(3,4)`,
- a generalized auditor (`scripts/check_parametric_cnf.py`),
- a generalized `minlib` witness structure with no hidden two-voter assumptions,
- clean audits for the generalized `(2,4)`, `(2,5)`, and `(3,4)` runs.

The concrete commands, counts, and CNF hashes are recorded in `docs/schema_generalization_tasklist.md`.

---

## Claim-scope restriction

The remaining Step 0.5 issue is **not** schema identity.
It is the effective-strength drift of `no_cycle3` and `no_cycle4` when `m=5` allows longer cycles.

This memo resolves that issue with the following restriction:

> Any Candidate A evidence obtained using `no_cycle3` and `no_cycle4` is interpreted only within the local-rationality family defined by those clause families. It is not, at Step 0.5, evidence about full `SocialAcyclic` or about families using a stronger rationality encoding.

Under this policy:

- Step 0 confirms that the same local clause families are instantiated across `(2,4)`, `(2,5)`, and `(3,4)`.
- Step 0.5 accepts that effective strength changes at `m=5`.
- Candidate A evidence remains usable, but only under the restricted local-rationality reading.

---

## Lever-by-Lever Analysis

### `asymm` — Asymmetry

**Lean-side target schema**  
The social strict relation is asymmetric.

**CNF-side finite instance pattern**  
For each profile `p` and ordered pair of distinct alternatives `(a,b)`:

- `¬P_p(a,b) ∨ ¬P_p(b,a)`

**Scaling judgment**  
This family is structurally unchanged. Only the number of profiles and ordered pairs changes.

| Check | Status |
|---|---|
| Same logical form across cases | ✓ confirmed |
| CNF clause structure invariant | ✓ confirmed |
| Candidate A usable? | ✓ yes |
| Scope restriction needed? | No |

---

### `un` — Unanimity (Pareto)

**Terminology correction**  
`un` is **Unanimity / Weak Pareto**, not Universal Domain.

**Lean-side target schema**  
If all voters prefer `x` to `y`, then the social relation ranks `x` above `y`.

**CNF-side finite instance pattern**  
For each profile `p` and ordered pair `(a,b)`:

- if all voters in `p` strictly prefer `a` to `b`,
- require the social relation at `p` to contain `a > b`.

**Scaling judgment**  
The generalized encoder now quantifies over all voters in the schema. The clause family is uniform across `(2,4)`, `(2,5)`, and `(3,4)`.

| Check | Status |
|---|---|
| Correctly identified as Pareto, not Universal Domain | ✓ confirmed |
| Quantifier structure not hard-coded to `n=2` | ✓ confirmed |
| Clause family uniform across cases | ✓ confirmed |
| Candidate A usable? | ✓ yes |
| Scope restriction needed? | No |

---

### `minlib` — Minimal Liberalism

**Lean-side target schema**  
There exist at least two distinct individuals `i ≠ j`, each decisive over at least one pair.

**CNF-side finite instance pattern**  
The generalized path uses:

- one selector for each unordered pair of distinct voters,
- one decisive-witness variable for each `(voter, ordered pair)`,
- support clauses ensuring each selected voter has at least one decisive pair witness,
- profile-local implications enforcing decisiveness.

**Scaling judgment**  
This resolves the Step 0 blocker. The existential structure is now parametric and does not depend on fixed voter identities.

| Check | Status |
|---|---|
| Existential quantification over individuals is parametric | ✓ confirmed |
| No hard-coded individual indices | ✓ confirmed |
| Distinctness of two decisive individuals preserved at `n=3` | ✓ confirmed |
| Candidate A usable? | ✓ yes |
| Scope restriction needed? | No |

---

### `no_cycle3` — Local 3-cycle prohibition

**Lean-side target schema**  
This lever is a **local forbidden-pattern approximation**, not full `SocialAcyclic`.

**CNF-side finite instance pattern**  
For each profile `p` and each ordered triple of distinct alternatives `(a,b,c)`:

- `¬P_p(a,b) ∨ ¬P_p(b,c) ∨ ¬P_p(c,a)`

**Step 0 result**  
Step 0 confirmed schema-level uniformity of this local clause family across `(2,4)`, `(2,5)`, and `(3,4)`.

**Remaining issue**  
At `m=5`, `no_cycle3 ∧ no_cycle4` still permits length-5 cycles, so the effective rationality constraint is weaker than it is at `m=4`.

**Step 0.5 resolution**  
This is resolved by explicit claim-scope restriction:

- the experiment may proceed,
- Candidate A evidence is usable,
- but only for the local-rationality family defined by `no_cycle3` and `no_cycle4`,
- not as evidence about full acyclicity families.

| Check | Status |
|---|---|
| Same local clause family across cases | ✓ confirmed |
| Remaining issue is effective-strength drift, not schema identity | ✓ confirmed |
| Candidate A usable? | ✓ yes, under restricted local-rationality scope |
| Stronger encoding required now? | No |

---

### `no_cycle4` — Local 4-cycle prohibition

**Lean-side target schema**  
As with `no_cycle3`, this lever is a **local forbidden-pattern approximation**, not full `SocialAcyclic`.

**CNF-side finite instance pattern**  
For each profile `p` and each ordered 4-tuple of distinct alternatives `(a,b,c,d)`:

- `¬P_p(a,b) ∨ ¬P_p(b,c) ∨ ¬P_p(c,d) ∨ ¬P_p(d,a)`

**Step 0 result**  
Step 0 confirmed schema-level uniformity of this local clause family across `(2,4)`, `(2,5)`, and `(3,4)`.

**Remaining issue**  
At `m=5`, banning all 4-cycles still does not imply full acyclicity because 5-cycles remain available.

**Step 0.5 resolution**  
This is resolved by the same claim-scope restriction:

- the experiment may proceed,
- Candidate A evidence is usable,
- but only inside the local-rationality family defined by `no_cycle3` and `no_cycle4`,
- not as evidence about full acyclicity families.

| Check | Status |
|---|---|
| Same local clause family across cases | ✓ confirmed |
| Remaining issue is effective-strength drift, not schema identity | ✓ confirmed |
| Candidate A usable? | ✓ yes, under restricted local-rationality scope |
| Stronger encoding required now? | No |

---

## Combined Status Table

| Lever | Schema uniform? | Effective-strength drift? | Candidate A usable? | Usability scope |
|---|---|---|---|---|
| `asymm` | ✓ | Low | ✓ | unrestricted |
| `un` (= Pareto) | ✓ | Low | ✓ | unrestricted |
| `minlib` | ✓ | Low for Step 0.5 purposes | ✓ | unrestricted |
| `no_cycle3` | ✓ | Medium at `m=5` | ✓ | restricted to local-rationality setting |
| `no_cycle4` | ✓ | Medium at `m=5` | ✓ | restricted to local-rationality setting |

---

## Decision Gate

**Proceed with the repair liftability experiment if:**

1. the parametric encoder and auditor are implemented,
2. schema uniformity is confirmed for all five levers,
3. `minlib` is verified to be genuinely parametric at `n=3`,
4. any use of `no_cycle3` / `no_cycle4` is explicitly interpreted under the local-rationality scope restriction stated above.

**Do not overclaim:**

- Do not reinterpret a `(2,5)` result as evidence about full `SocialAcyclic`.
- Do not describe this experiment as comparing full acyclicity families unless a stronger rationality encoding is added later.

Under those conditions, the experiment is cleared to run.

---

## Sign-off

- [x] `asymm`: schema confirmed uniform, clause structure verified
- [x] `un` (Pareto): schema confirmed uniform, not confused with Universal Domain
- [x] `minlib`: existential structure verified at `n=3`, no hard-coded indices
- [x] `no_cycle3`: schema uniform; remaining issue resolved by explicit restricted-scope interpretation
- [x] `no_cycle4`: schema uniform; remaining issue resolved by explicit restricted-scope interpretation
- [x] Generalized auditor produces clean audit for all three cases
- [x] Experiment cleared to run under the `no_cycle3` / `no_cycle4` local-rationality interpretation

---

## Sign-off statement

This memo is signed off for Step 0.5 under the following condition:

> The repair liftability experiment may be used as Candidate A evidence only within the local-rationality family defined by `no_cycle3` and `no_cycle4`, unless a stronger rationality encoding is introduced in later work.
