# 3-Row Test Completed

**Status: COMPLETED as of 2026-04-01 (Candidate B branch)**

This note records the completed 3-row test for the Auditability Separation Theorem (working title).
It matters because it fixes the current repository-level statement of what must be shown, what has now been shown,
and which evidence source discharges each layer of the argument.

## Audit Trail

- Experiment execution date: `2026-04-01`
- Results directory: `results/20260401/candidate_b_minlib_granularity/`
- Branch: `codex/candidate-b-minlib-granularity`
- Reference commit hash: `aa2e2c433920efb7b7104aadf69b77be9efe552b`

---

## Row 1 — Definition

A finite-case impossibility result φ at (n₀, m₀) is an **auditable witness** for family F iff:

1. The UNSAT/SAT evidence at (n₀, m₀) is mechanically verifiable.
2. The family F that φ claims about, and the transfer assumptions
   (reduction / induction / finite-model assumptions) needed to move from
   base case to F, are explicitly declared.
3. A legitimacy rule is attached: family-level claims may not be made
   unless the declared transfer assumptions are satisfied.
4. In the UNSAT case, at least one mechanically checkable minimal repair basis is provided.

---

## Row 2 — Separation Proposition (Auditability Separation, refined)

In a Sen-type family, reduction holds and the finite witness can be legitimately
used at family level. However, even when reduction holds, and even when two
base-case encodings are logically equivalent (in this experiment: exact
clause-multiset equivalent at (2,4)), the minimal repair basis is not
representation-invariant.

Therefore auditability is not exhausted by reduction/FMP.
Family-level witness legitimization and repair explanation canonicality are
separate problems.

The reason this separates Sen from Arrow (理由Y):
In the Sen-type case, reduction holds, so the problem reaches the
repair-canonicalization layer.
In the Arrow-type case, individual-dimension finite model property fails
(Grandi–Endriss), so the finite-to-general transfer is not generally guaranteed,
and the problem stops at the witness-legitimization layer before repair
canonicalization is even reached.

Concrete evidence from Candidate B:
Bundled `asymm+un+minlib+no_cycle4` and split
`asymm+un+decisive_voter0+decisive_voter1+no_cycle4` are exact clause-multiset
equivalent at (2,4). Nevertheless, minimal repairs diverge:
bundled side yields `{minlib}`, split side yields `{decisive_voter0}` and
`{decisive_voter1}`. Repair explanation is granularity-sensitive.

---

## Row 3 — Proof Resources

Two layers:

Layer 1: Use Grandi–Endriss / Geist–Endriss to characterize when finite witnesses
can be lifted to family-level claims, and when that justification breaks.
Specifically: Geist–Endriss provides a general result that, for principles in an
appropriate many-sorted first-order syntactic form, impossibility found at small
fixed size lifts to the general case.

Layer 2: Use the Candidate B experiment to show that even when family-level use
is justified and the base-case encodings are logically equivalent, minimal repair
basis is not representation-invariant. This grounds the decomposition of
auditability into two independently required conditions:
(a) finite witness legitimization condition
(b) repair explanation canonicality condition

---

## Evidence Sources

- Row 1 evidence source: `ZENODO_CLAIMS.md` and `docs/experiment_protocol_repair_liftability.md`.
- Row 2 evidence source: `results/20260401/candidate_b_minlib_granularity/summary.md` and Grandi–Endriss (2013).
- Row 3 evidence source: Geist–Endriss (2011) and the Candidate B artifact bundle under `results/20260401/candidate_b_minlib_granularity/`.

## Reading Note

The completed Row 2 proposition now explicitly records the previously open 理由Y slot.
That slot is filled by the Candidate B base-case comparison: in the Sen-type setting the transfer problem is not what blocks progress,
so the analysis reaches the repair-canonicalization layer; in the Arrow-type setting the transfer problem itself can fail first.

All conclusions in this note remain subject to the repository's current scope restriction:
`no_cycle3` and `no_cycle4` are treated as local-rationality approximations, not as full `SocialAcyclic`.
