# Candidate A Collapse Note
## Why the repair liftability experiment collapsed at the current axiom granularity

**Status:** Observation recorded after completing Steps 1–3 of the repair liftability experiment.  
**Date:** 2026-04-01  
**Related:** `docs/experiment_protocol_repair_liftability.md`, `results/20260401/repair_liftability/`

---

## What was attempted

The repair liftability experiment (Steps 1–3) tested whether base-case minimal repairs
lift to neighboring cases `(2,5)` and `(3,4)` within the five-lever family
`{asymm, un, minlib, no_cycle3, no_cycle4}`.
For each of the two base-case UNSAT packages, all inclusion-minimal repairs were enumerated
and each was applied to the larger cases.
The experiment was designed to look for repair non-liftability as evidence for
Candidate A of the Auditability Separation Theorem: that auditability is not equivalent
to reduction/FMP.

## Why the experiment collapsed

Every base-case MCS turned out to have size 1.
This means each UNSAT package can be repaired by removing any single axiom,
and no repair requires removing two or more axioms simultaneously.
As a consequence, the local minimality check for each repair
reduces to re-testing whether the original UNSAT package remains UNSAT in the larger case —
which it does, since impossibility scales across `(2,4)`, `(2,5)`, and `(3,4)` for this family.
All 16 Step 3 checks returned UNSAT, confirming local minimality trivially.
There is no structural variation in the repair set across case sizes:
the experiment cannot distinguish between "repair structure is preserved" and
"the impossibility is so rigid that every single-axiom removal is a valid repair everywhere."
At this axiom granularity, the liftability experiment is self-collapsing.

## What is needed to run a non-trivial version

A non-trivial repair liftability experiment requires at least one MCS of size ≥ 2.
Only then can the experiment detect repair asymmetry: a situation where
`R = {r₁, r₂}` is minimal at the base case but `{r₁}` alone suffices in a larger case,
which would constitute concrete evidence for Candidate A.
This can be achieved by either (a) refining the axiom encoding so that individual levers
are no longer sufficient repairs on their own — for example, by splitting a lever into
sub-conditions that must be jointly removed — or (b) working with a richer impossibility
theorem whose MCS structure is intrinsically more complex.
The present observation is therefore not a failure of the experiment protocol,
but a necessary constraint on what axiom granularity is required for the protocol to be informative.
Recording this constraint is itself a contribution to the audit framework design:
the choice of axiom granularity is not neutral, and experiments that collapse at size-1 MCS
must be redesigned before they can serve as separation evidence.
