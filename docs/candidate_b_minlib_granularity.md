# Candidate B: Minlib Granularity
## Base-case experiment design memo

**Branch intent:** `codex/candidate-b-minlib-granularity`  
**Main question:** does repair explanation change when the same base-case impossibility is represented with different `minlib` granularity?  
**Scope:** base case only, `(n,m) = (2,4)`, inside the existing `no_cycle3` / `no_cycle4` local-rationality family.

---

## Why Candidate B is now the main branch

Candidate A was tested first using neighboring cases and the restricted local-rationality interpretation.
The current Step 1–3 artifacts show:

- all tested base-case repairs lift to `(2,5)` and `(3,4)`,
- all tested repairs remain locally minimal there,
- Candidate A is therefore substantially weakened for the currently tested family.

That makes encoding sensitivity the next clean target.

The most promising axis is not `no_cycle3` / `no_cycle4` bundling.
Those levers are already burdened by the Step 0.5 scope restriction at `m=5`.
The cleaner comparison is `minlib` granularity at the unchanged base case `(2,4)`.

---

## Why minlib granularity is the main comparison

In the bundled representation, `minlib` is one existential lever.
Its repair explanation is therefore also bundled: a size-1 repair may simply be `{minlib}`.

In the split representation, the same liberalism layer is exposed through two separate levers:

- `decisive_voter0`
- `decisive_voter1`

This allows one side of the liberalism requirement to be dropped independently of the other.
If the same impossibility then yields person-specific repairs such as `{decisive_voter0}` or `{decisive_voter1}`,
the repair explanation depends on encoding granularity rather than only on theorem content.

---

## Why the experiment is restricted to `(2,4)`

This branch stays at the base case on purpose.

Reasons:

- it avoids conflating Candidate B with Step 0 scaling issues,
- it avoids reintroducing the Step 0.5 `m=5` interpretation caveat as the main moving part,
- it makes the logical relation between bundled and split `minlib` maximally controlled,
- it keeps the evidence bundle small and auditable.

The branch does **not** broaden claims beyond the current restricted local-rationality family.

---

## Representations

### Representation A — bundled `minlib`

Lever family:

- `asymm`
- `un`
- `minlib`
- `no_cycle3`
- `no_cycle4`

### Representation B — split `minlib`

Lever family:

- `asymm`
- `un`
- `decisive_voter0`
- `decisive_voter1`
- `no_cycle3`
- `no_cycle4`

The intended correspondence is:

`minlib`  ↔  `decisive_voter0 ∧ decisive_voter1`

---

## Logical relation between bundled and split `minlib`

At `(2,4)`, the split encoding is **logically equivalent** to the bundled encoding under the natural mapping
`minlib ↔ decisive_voter0 ∧ decisive_voter1`.

In fact, the current implementation establishes a stronger engineering fact:

- for every bundled package in the 5-lever universe,
- the corresponding split package obtained by replacing `minlib` with both decisive levers
- has the same CNF clause multiset.

So the mapped bundled and split packages are not merely satisfiability-equivalent.
They are clause-set equivalent modulo lever partitioning.

This matters because any repair-structure difference observed between:

- `{minlib}` in the bundled world, and
- `{decisive_voter0}` / `{decisive_voter1}` in the split world

cannot be explained by a stronger split encoding in this experiment.

---

## What counts as positive evidence for Candidate B

Positive evidence is ranked as follows:

### Level 1

Same underlying impossibility, but the bundled representation yields `{minlib}` while the split representation yields person-specific repairs such as `{decisive_voter0}` or `{decisive_voter1}`.

### Level 2

Same UNSAT frontier under the bundled→split mapping, but different MCS identities under different lever granularity.

### Level 3

Same clause content at the liberalism layer, but different repair explanations.

### Level 4

A representation-invariant canonical repair explanation cannot be defined without adding extra grouping conventions.

---

## Current result on this branch

The first clean base-case run achieves the strongest reading needed for Candidate B:

- mapped bundled and split packages have the same UNSAT frontier,
- mapped bundled and split packages are clause-set equivalent,
- bundled `{minlib}` repairs refine into split `{decisive_voter0}` and `{decisive_voter1}` repairs,
- therefore the repair explanation changes under pure granularity refinement.

This is direct Candidate B evidence under logical equivalence, not a stronger-encoding artifact.

The machine artifacts live under:

- `results/20260401/candidate_b_minlib_granularity/`

The main comparison summary is:

- `results/20260401/candidate_b_minlib_granularity/summary.md`

---

## Interpretation discipline

All Candidate B conclusions in this branch remain restricted to the current local-rationality family:

- `no_cycle3`
- `no_cycle4`

This branch does **not** claim anything about full `SocialAcyclic`.

If stronger rationality is introduced later, Candidate B would need a new controlled comparison rather than reusing this branch’s conclusion without qualification.
