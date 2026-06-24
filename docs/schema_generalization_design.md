> Historical design note. This document records an earlier direct-lifting / schema-generalization plan. The current canonical research-program status is maintained in `docs/research_program_current.md`. In particular, M2 now establishes a semantic obstruction bridge, while CNF/LRAT/atlas/repair transfer remains outside the claim boundary.

# Schema Generalization Design Memo
## Step 0 for Repair Liftability Experiment

**Status:** Step 0 implementation landed in code on 2026-03-31; this memo remains the design reference for the resulting evidence.  
**Location:** `docs/schema_generalization_design.md`  
**Feeds into:** `docs/axiom_semantics_scaling.md` → `docs/experiment_protocol_repair_liftability.md`

---

## 1. Why this exists

The current repository is architected around the fixed Sen24 base case `(n,m) = (2,4)`.

This is visible at three levels:

1. the finite schema layer is effectively Sen24-scoped,
2. the current CNF generator exposes `--n` and `--m` but documents support only for `n=2`, `m=4`,
3. the current auditor/checker path is likewise Sen24-specific.

Therefore, the repair liftability experiment over:

- `(2,4)`
- `(2,5)`
- `(3,4)`

cannot be treated as trustworthy until a **parametric schema** and **parametric auditor**
exist and the five experimental levers are shown to be size-variants of the same schema.

This memo defines the required Step 0.

---

## 1.5 Current implementation status

The repository now contains the Step 0 code path described below:

- `encoding/schema.py` now exposes a parametric `FiniteSchema(n, m, minlib_mode=...)`.
- `Sen24Schema(...)` remains as a backward-compatible wrapper for the legacy `(2,4)` workflow.
- `scripts/gen_dimacs.py` now generates `(2,4)`, `(2,5)`, and `(3,4)` from the same schema layer.
- `scripts/check_parametric_cnf.py` audits the generalized schema family without silently assuming `m=4`.
- The committed Sen24 artifact path is preserved by keeping legacy `minlib` mode `selectors_v1` as the default compatibility mode at `(2,4)`.
- Neighboring cases use parametric `minlib` mode `pair_selectors_v1`, which removes fixed two-voter selector assumptions.

Concrete audit evidence and commands are recorded in `docs/schema_generalization_tasklist.md`.

---

## 2. Design objective

Create a parametric finite-schema and auditing layer such that the following question becomes mechanically meaningful:

> Are `asymm`, `un`, `minlib`, `no_cycle3`, and `no_cycle4`
> interpreted as instances of the same logical schema across `(2,4)`, `(2,5)`, and `(3,4)`?

This memo is not a theorem memo.
It is a design memo for making the later semantics-scaling sign-off evidentially defensible.

---

## 3. Core principle

“Same schema” does **not** mean same clause count.

It means:

1. the **quantifier skeleton** is unchanged,
2. only the size of the quantified finite sets changes,
3. the role of each variable family is unchanged,
4. enabling a lever still acts as a monotone clause addition,
5. any **effective-strength change** is documented separately.

This last point is crucial for `no_cycle3` and `no_cycle4`.

---

## 4. What must be generalized

### 4.1 Parametric finite schema

Replace the effectively fixed `Sen24Schema` usage with a parametric finite schema abstraction, e.g.:

- `FiniteSchema(n: int, m: int, ...)`

The generalized schema should expose at least:

- `n_voters`
- `n_alts`
- `voters`
- `alts`
- `profiles`
- `pairs`
- `triples`
- `quads`

and helper functions for preference/profile lookup.

### 4.2 Backward-compatible Sen24 wrapper

Preserve a convenience wrapper such as:

- `Sen24Schema() := FiniteSchema(n=2, m=4, ...)`

so the current Sen24 workflow remains stable.

### 4.3 Parametric auditor

The current checker path is Sen24-oriented.
A generalized checker must validate arbitrary tested `(n,m)` instances without silently assuming `m=4`.

A separate script such as:

- `scripts/check_parametric_cnf.py`

is acceptable if retrofitting the existing Sen24 checker is too risky.

---

## 5. Lever-by-lever target semantics

---

## 5.1 `asymm`

### Intended schema

For each profile `p` and each ordered pair of distinct alternatives `(a,b)`:

- forbid simultaneous social strict preference of both `a > b` and `b > a`

In CNF form:

- `¬P_p(a,b) ∨ ¬P_p(b,a)`

where `P_p(a,b)` is the **social preference variable at profile `p`**.

### Generalization requirement

The encoder must iterate over:

- all profiles in the parametric schema,
- all ordered alternative pairs in the parametric schema.

### What must remain invariant

- profile-local social relation semantics
- anti-symmetry clause pattern
- monotone toggle behavior

### What may change

- number of profiles
- number of pairs
- total clause count

### Sign-off criterion

`asymm` is sign-off-safe if it remains purely size-parametric and introduces no special treatment of particular voter or alternative indices.

---

## 5.2 `un`

### Terminology correction

In this repository, `un` must be interpreted as:

- **Unanimity / Weak Pareto**

not as Universal Domain / Unrestricted Domain.

Universal Domain is an ambient assumption, not a leverized clause family.

### Intended schema

For each profile `p` and ordered pair `(a,b)`:

- if all voters in profile `p` strictly prefer `a` to `b`,
- then the social relation at `p` must contain `a > b`.

### Generalization requirement

The current fixed-voter helper logic must be replaced by a truly parametric “all voters prefer `a` over `b`” test.

That means:

- profile representation must support arbitrary `n`,
- unanimity must quantify over all voters,
- no reliance on exactly two voter positions may remain.

### What must remain invariant

- universal voter quantification
- profile-local implication to social preference
- monotone toggle behavior

### What may change

- number of unanimity-triggering profiles
- clause count

### Sign-off criterion

`un` is safe only if its generalized encoder is explicitly aligned with the Lean-side `UN` semantics.

This lever must be treated as profile-local unanimity-to-social-preference implication, not as a domain restriction lever.

---

## 5.3 `minlib`

### Intended schema

There exist at least two **distinct** individuals, each decisive over at least one pair of alternatives.

This is the finite encoding target corresponding to Lean-side minimal liberalism.

### Why this is the hardest blocker

The current Python-side encoding is tied to two-voter machinery via structures like:

- `pref0`, `pref1`
- `var_sel0`, `var_sel1`

So `minlib` is not presently sign-off-ready for `(3,4)`.

### Generalization requirement

Replace fixed two-voter selector logic with a parametric decisiveness encoding over arbitrary voter indices.

The design must explicitly support:

- voter-indexed decisiveness witnesses,
- existence of two distinct decisive voters,
- at least one decisive pair per selected voter.

### Acceptable implementation strategies

#### Option A — Generalized selector family
Introduce selector variables indexed by voter and pair.

#### Option B — Direct existential compilation
Compile the existential witness structure directly into CNF.

Either is acceptable, but the resulting semantics must not depend on fixed voter identities.

### What must remain invariant

- existential shape of the schema
- distinctness of the two decisive voters
- meaning of decisiveness

### What may change

- number of witness candidates
- clause count
- SAT difficulty

### Sign-off criterion

`minlib` remains a **blocker** until it is detached from two-voter hardcoding.

---

## 5.4 `no_cycle3`

### Intended schema

For each profile `p` and each ordered triple of distinct alternatives `(a,b,c)`:

- forbid simultaneous `a > b`, `b > c`, `c > a` in the social relation.

### Important conceptual status

`no_cycle3` is **not** the full Lean-side `SocialAcyclic`.
It is a local finite forbidden-pattern approximation.

### Generalization requirement

Generate clauses over all profile-local triples in the parametric schema.

### What must remain invariant

- local 3-cycle prohibition pattern
- social-variable semantics
- monotone toggle behavior

### What may change

- number of triples
- effective strength relative to full acyclicity
- interaction with `no_cycle4`

### Sign-off criterion

`no_cycle3` is sign-off-safe only if the scaling memo explicitly records that it is a local approximation, not full acyclicity.

---

## 5.5 `no_cycle4`

### Intended schema

For each profile `p` and each ordered 4-tuple of distinct alternatives `(a,b,c,d)`:

- forbid simultaneous `a > b`, `b > c`, `c > d`, `d > a`.

### Important conceptual status

As with `no_cycle3`, this is a local approximation rather than the full Lean-side `SocialAcyclic`.

### Generalization requirement

Generate clauses over all profile-local 4-tuples in the parametric schema.

### What must remain invariant

- local 4-cycle prohibition pattern
- social-variable semantics
- monotone toggle behavior

### What may change

- number of 4-tuples
- effective strength as `m` grows
- relationship to full acyclicity

### Sign-off criterion

`no_cycle4` is sign-off-safe only if the scaling memo explicitly records that:

- `no_cycle3 ∧ no_cycle4` may behave unusually well at `m=4`,
- but does not guarantee full acyclicity at `m=5`.

---

## 6. Auditor requirements

A generalized schema alone is not sufficient.
A generalized auditor must also exist.

The auditor should verify, for tested `(n,m)`:

- schema dimensions
- enabled lever set
- variable family discipline
- profile indexing discipline
- pair / triple / quad enumeration discipline
- clause-shape validity for each enabled lever
- expected category counts where derivable

If retrofitting the existing Sen24 checker is risky, add a separate parametric checker.

---

## 7. Documentation changes required

### 7.1 Update `docs/axiom_semantics_scaling.md`

It must be revised so that:

- `un` is described as Unanimity / Weak Pareto
- `minlib` is marked blocker until generalized
- `no_cycle3/4` are described as local acyclicity approximations
- “same schema” and “effective strength” are explicitly separated

### 7.2 Keep `docs/experiment_protocol_repair_liftability.md` but add dependency note

The experiment protocol itself is sound, but it is blocked on Step 0:

> parametric schema + parametric auditor + semantics-scaling evidence

### 7.3 Optional companion document

Optionally add:

- `docs/schema_generalization_tasklist.md`

for file-by-file implementation tasks.

---

## 8. Suggested implementation order

### Phase 1 — Parametric schema abstraction
1. implement parametric finite schema
2. preserve Sen24 wrapper
3. route generation entrypoints through the parametric schema

### Phase 2 — Easy local lever generalization
1. `asymm`
2. `no_cycle3`
3. `no_cycle4`

### Phase 3 — Generalize `un`
1. replace two-voter unanimity logic with all-voter logic
2. align documentation with Lean-side `UN`

### Phase 4 — Generalize `minlib`
1. remove fixed two-voter selector assumptions
2. support arbitrary voter indices
3. validate distinct-witness semantics

### Phase 5 — Parametric auditor
1. implement generalized CNF checker
2. test `(2,4)`, `(2,5)`, `(3,4)`

### Phase 6 — Semantics scaling sign-off
1. fill in all five levers with evidence
2. document effective-strength caveats
3. sign off only after Step 0 evidence exists

---

## 9. Definition of done for Step 0

All of the following must hold before proceeding to experimental sign-off:

- [ ] parametric schema exists for tested neighboring cases
- [ ] `asymm`, `un`, `minlib`, `no_cycle3`, `no_cycle4` are implemented against that schema
- [ ] `minlib` no longer depends on fixed two-voter logic
- [ ] generalized auditor validates tested CNFs
- [ ] `docs/axiom_semantics_scaling.md` is filled using evidence, not conjecture
- [ ] `no_cycle3/4` effective-strength caveats are documented

---

## 10. Decision rule

If Step 0 succeeds:
- proceed to `axiom_semantics_scaling.md` sign-off
- then run repair liftability experiment

If Step 0 succeeds but `no_cycle3/4` remain interpretively confounded:
- either replace them with a stronger rationality encoding,
- or reclassify the result as Candidate B material

If `minlib` generalization fails:
- do not sign off
- do not run the repair liftability experiment
- treat schema generalization itself as the immediate engineering priority

---

## 11. Summary

The immediate bottleneck is not the repair experiment itself.

The bottleneck is that the current repository still embodies a Sen24-fixed finite schema.

Therefore the next required step is:

> generalize the finite schema and the auditor so that lever meanings can be compared across `(2,4)`, `(2,5)`, and `(3,4)` as size-variants of the same schema.

Only after that can `docs/axiom_semantics_scaling.md` be signed off and the repair liftability experiment be trusted.
