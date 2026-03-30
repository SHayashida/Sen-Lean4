# Axiom Semantics Scaling Memo
## Prerequisite for Repair Liftability Experiment

**Status:** Must be completed before running `experiment_protocol_repair_liftability.md`  
**Location:** `docs/axiom_semantics_scaling.md`

---

## Purpose

This memo confirms that all axiom levers used in the repair liftability experiment
are interpreted as instances of the **same axiom schema** across different case sizes.

If lever semantics change as (n, m) grows, observed non-liftability could be an artifact
of semantic drift rather than genuine repair structure change.
This would invalidate the experiment's conclusions.

---

## Cases Under Examination

| Case | n (voters) | m (alternatives) |
|---|---|---|
| Base | 2 | 4 |
| Larger-1 | 2 | 5 |
| Larger-2 | 3 | 4 |

---

## Lever-by-Lever Analysis

### `asymm` — Asymmetry

**Schema:** For all individuals i, alternatives x, y: if xPᵢy then ¬yPᵢx.

**Scaling behavior:** Quantifies over all pairs within each individual's preference.
Number of CNF clauses scales with m(m−1)/2 per individual, but the schema is identical.

**Status:** ☐ Confirmed uniform across (2,4), (2,5), (3,4)

---

### `un` — Unrestricted Domain / Universal Domain

**Schema:** All preference profiles over the alternatives are in the domain.

**Scaling behavior:** In CNF encoding, this is typically implicit (no domain restriction clauses).
Confirm that the encoding does not introduce profile filtering for larger (n, m).

**Status:** ☐ Confirmed uniform across (2,4), (2,5), (3,4)

---

### `minlib` — Minimal Liberalism

**Schema:** There exist at least two individuals each of whom is decisive over at least one pair.

**Scaling behavior:** The schema quantifies existentially over individuals and pairs.
With more individuals (n=3) or more alternatives (m=5), the condition becomes *easier* to satisfy
(more candidates for decisive pairs), but the schema itself is unchanged.

**Key check:** Confirm that the CNF encoding uses the same existential structure and
does not hard-code individual indices in a way that changes meaning at n=3.

**Status:** ☐ Confirmed uniform across (2,4), (2,5), (3,4)

---

### `no_cycle3` — Acyclicity (length 3)

**Schema:** For all triples of alternatives x, y, z:
¬(xPy ∧ yPz ∧ zPx) in the social preference.

**Scaling behavior:** ⚠️ **Requires careful attention.**

At m=4, the number of triples is C(4,3) = 4.
At m=5, the number of triples is C(5,3) = 10.

The schema is the same, but:
- The condition covers more triples at larger m.
- `no_cycle3` alone may be *weaker relative to* `no_cycle4` at larger m,
  because longer cycles become available.

**Key question:** Is `no_cycle3` at (2,5) or (3,4) the same *normative constraint*
as at (2,4), or does it permit more pathological structures due to additional alternatives?

**Status:** ☐ Analyzed — see notes below

*Notes:*
> [Fill in after analysis]

---

### `no_cycle4` — Acyclicity (length 4)

**Schema:** For all 4-tuples of alternatives x, y, z, w:
¬(xPy ∧ yPz ∧ zPw ∧ wPx) in the social preference.

**Scaling behavior:** ⚠️ **Requires careful attention.**

At m=4, there is exactly C(4,4) = 1 four-cycle to prohibit.
At m=5, there are C(5,4) = 5 four-cycles.
At (n=3, m=4), the number of four-cycles is the same as (n=2, m=4),
but the social preference function maps from a larger profile space.

**Key question:** Does the combined `no_cycle3 ∧ no_cycle4` impose the same
*effective* rationality constraint at (2,5) and (3,4) as at (2,4)?

**Status:** ☐ Analyzed — see notes below

*Notes:*
> [Fill in after analysis]

---

## Combined Assessment

| Lever | Uniform schema? | Effective strength change? | Safe to use in experiment? |
|---|---|---|---|
| `asymm` | ☐ | Scales proportionally | ☐ |
| `un` | ☐ | No change expected | ☐ |
| `minlib` | ☐ | Easier to satisfy at larger n,m | ☐ |
| `no_cycle3` | ☐ | **Covers more triples — check** | ☐ |
| `no_cycle4` | ☐ | **Covers more tuples — check** | ☐ |

---

## Decision Gate

**Proceed with experiment if:**
All levers are confirmed as instances of the same schema, AND
any effective strength changes are documented and judged not to confound
the repair liftability results.

**Block experiment if:**
`no_cycle3` or `no_cycle4` impose qualitatively different constraints at larger (n, m)
in a way that could produce spurious non-liftability.

In the blocking case, consider either:
1. Replacing `no_cycle3/4` with a uniform acyclicity condition (`SocialAcyclic` in Lean spec), or
2. Treating the encoding difference as Candidate B material (encoding sensitivity).

---

## Sign-off

- [ ] Axiom semantics confirmed
- [ ] Decision gate passed
- [ ] Experiment cleared to run
