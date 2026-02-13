# Assumptions: Symmetry Reduction Safety (alts)

## Scope

This note specifies the safety contract for `scripts/run_atlas.py --symmetry alts` in sen24.

## What `--symmetry alts` means

- We consider the action of relabeling alternatives (`S_4` on `{0,1,2,3}`).
- Cases are grouped into equivalence classes using semantic outputs (not CNF text fingerprints).
- Atlas metadata records:
  - `equiv_class_id`
  - `representative_case` (lexicographically smallest case id)
  - `orbit_size`

## Soundness condition

`symmetry=alts` is sound **iff** every enabled axiom encoding is invariant under alternative relabeling.

In practical terms:

- no axiom may hard-code a distinguished labeled alternative role,
- no axiom may branch on specific alternative IDs in a way that breaks relabeling invariance.

## Enforcement in code

Axiom modules publish capability metadata:

- `SUPPORTS_SYMMETRY_ALTS: bool`

`run_atlas.py` behavior:

- if `--symmetry alts` and any selected axiom has `SUPPORTS_SYMMETRY_ALTS != True`,
  the run fails fast with an explicit list of violating axioms.
- override is possible via `--symmetry-unsafe-ok` (for controlled experiments only).

## Symmetry check (engineering guardrail)

Symmetry is treated as a compute heuristic; correctness guardrail is:

- optional `--symmetry-check`,
- deterministic sampling of non-representative members,
- direct re-solve and status comparison against class representative.

Recorded in `atlas.json`:

- `symmetry_check.checked_k`
- `symmetry_check.mismatches`
- `symmetry_check.checked_cases`
- top-level `checked_cases` (same IDs, for quick audit)

Any mismatch aborts the run.

## What this does NOT claim

- This does not prove full group-action correctness in Lean.
- It gives an auditable engineering safety contract with explicit metadata + runtime checks.
