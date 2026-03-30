# Experiment Protocol v0.1
## Repair Liftability Test — Sen-type family

**Status:** Pre-experiment spec (not yet run)  
**Location:** `docs/experiment_protocol_repair_liftability.md`  
**Prerequisite:** `docs/axiom_semantics_scaling.md` must be completed before running.

---

## Goal

> Test whether base-case repairs are legitimate as family-level repair bases in a family where reduction holds.
> If liftability fails, treat this as candidate evidence for **auditability ≠ reduction/FMP**.

This experiment targets **Candidate A** (repair non-liftability) in the separation table
for the Auditability Separation Theorem (working title).
A negative result (full liftability) is also informative: it would weaken Candidate A
and justify pivoting to Candidate B (encoding sensitivity).

---

## Prerequisites (Blockers — must be resolved before running)

See `docs/axiom_semantics_scaling.md` for the required axiom semantics memo.

Specifically, confirm that all five levers:

- `asymm`
- `un`
- `minlib`
- `no_cycle3`
- `no_cycle4`

are interpreted as instances of the **same axiom schema** across cases (2,4), (2,5), and (3,4).
In particular, `no_cyclek` may change in effective strength as case size grows;
this must be documented before results can be trusted.

---

## Inputs

| Item | Content |
|---|---|
| Base case | n=2, m=4 (existing Sen24 results) |
| Axiom levers | `asymm, un, minlib, no_cycle3, no_cycle4` (per existing manifest) |
| MCS candidates | All minimal repairs R from `mus_mcs.py` output (`mcs.json`) |
| Larger cases | (n=2, m=5) and (n=3, m=4) |

---

## Steps

### Step 1: Fix all base-case repair triples

For each UNSAT package A in the base case, extract **all** minimal repair candidates
R₁, R₂, …, Rₖ separately and record each as a distinct triple (A, Rᵢ, A \ Rᵢ).

> Rationale: A single A may have multiple MCS candidates.
> Treating them as separate rows allows detection of **repair asymmetry**:
> some repairs may lift while others do not, even from the same base package.

### Step 2: Apply each repair to larger cases

For each Rᵢ, apply A \ Rᵢ to the larger case and record SAT/UNSAT.

Using `gen_dimacs.py` with `--axioms` set to the levers in A \ Rᵢ.

### Step 3: Check repair minimality in the larger case

If A \ Rᵢ is SAT in the larger case, verify **local minimality** of Rᵢ there:

For each r ∈ Rᵢ, check whether A \ (Rᵢ \ {r}) is UNSAT in the larger case.

If this holds for all r, then Rᵢ is locally minimal in the larger case.

Additionally, if computationally feasible, re-extract the full MCS set for A in the
larger case and check whether Rᵢ appears in it.

---

## Output Table

| Base package A | Base MCS Rᵢ | Larger case | SAT under A\Rᵢ? | Rᵢ locally minimal? | Rᵢ in larger-case MCS set? | Interpretation |
|---|---|---|---|---|---|---|
| | | (2,5) | | | | |
| | | (3,4) | | | | |

---

## Interpretation Guide

| Pattern | Interpretation |
|---|---|
| SAT + locally minimal + in larger-case MCS set | Supports repair liftability |
| SAT + not locally minimal | Repair structure change — initial evidence of non-liftability |
| UNSAT | Strong non-liftability |
| SAT but not in larger-case MCS set | Non-canonical repair / family-level mismatch |
| Multiple base repairs, only some survive | Repair asymmetry — initial evidence for Candidate A |

---

## Reading the Overall Result

**All rows: SAT + locally minimal**
→ No separation found here. Candidate A is weakened.
Consider pivoting to Candidate B (encoding sensitivity / `docs/candidate_b_encoding_sensitivity.md`).

**At least one non-liftability pattern**
→ Continue with Candidate A. Promote that row as the concrete example for the core proposition.

**Results differ between (2,5) and (3,4)**
→ Family-size-dependent repair structure. Worth investigating further.

---

## Output Artifacts

Results go under `results/<YYYYMMDD>/repair_liftability/`:

```
results/<date>/repair_liftability/
├── base_triples.json        # (A, R, A\R) for all base UNSAT cases
├── liftability_table.csv    # output table
├── minimality_checks.json   # per-r UNSAT checks for each (R, larger case)
└── summary.md               # interpretation narrative
```

---

## Relationship to Core Proposition

This experiment directly tests the separation between:

- **reduction property** (Grandi–Endriss): transfer condition for impossibility
- **auditability** (working definition): legitimacy condition for using a result in design contexts

If repair non-liftability is found, this constitutes the first concrete evidence that
auditability is not equivalent to reduction/FMP — the key requirement for the
Auditability Separation Theorem to be a new theorem rather than a vocabulary revision.
