# M3 CURRENT-PAPER FREEZE

Date: 2026-09-27

Status:

```text
THEORY-COMPLETE FOR CURRENT PAPER
PRIOR-ART SYNCHRONIZED
ARTIFACT EVIDENCE COMPLETE FOR CURRENT CLAIM BOUNDARY
FURTHER THEORETICAL STRENGTHENING DEFERRED
```

This document defines the stopping point for the current M1.5+M3 paper. It is
a scope and status record, not a new theorem, experiment, or novelty proof.

## Canonicalization record

- completed synchronization branch: `codex/m3-manuscript-prior-art-sync`;
- prior-art matrix commit: `30f2c0a`;
- completed manuscript-sync commit:
  `bfabbb65b7c4604c4846a1d1cf9cff1f62da9b8f`;
- current-paper freeze commit:
  `9f1cd4cd83eac2cd8855941cddb2a4280e7a5952`;
- canonicalization PR:
  [#24](https://github.com/SHayashida/Sen-Lean4/pull/24);
- pre-canonicalization `origin/main`:
  `bf8153b5a4d06c0be7507b1840d162b8c3123a0f`;
- merge commit and authoritative post-merge `main`:
  `CANONICALIZATION_MERGE_PENDING`.

The PR merge record and final task report are the authoritative Git records
for the post-merge SHA.

## Frozen current-paper results

The following are current results or evidence within their declared boundaries:

- the M1.5 representation-sensitive raw-repair non-canonicity witness;
- M3-A, the atomic sufficient regime and its raw-transport result;
- M3-B grouped correctness under disjointness, residual faithfulness, and
  GroupSoundness;
- M3-C converse/exactness under target-side `PsiDeletionMonotonicity` and the
  other hypotheses of the combined equivalence;
- `audit_cost_collapse`, which does not assume deletion monotonicity of
  `SatPhi`;
- Candidate B as artifact-level evidence under its explicit claim boundary,
  not as a Lean theorem or semantic validation of its contract atoms;
- the frozen 7 x 8 prior-art claim matrix; and
- the synchronized integrated manuscript under
  `papers/cpp2027_m1_5_m3/`.

The current paper distinguishes implementation-level repair correctness from
correctness under an independently specified target reporting semantics.
`SatPhi` and `SatPsi` are separate predicates, while `ResidualFaithfulness`
provides the explicit block-aligned bridge; they are not treated as arbitrary
unrelated semantics.

## Explicit non-blockers for the current paper

Each item below is `DEFERRED — NOT A BLOCKER FOR CURRENT PAPER`:

- `GC <-> FS ∧ CRLift`;
- a new `FrontierSoundness` declaration;
- a new `CRLift` declaration;
- a weakest-than-atomic characterization;
- an incomplete-frontier assurance hierarchy;
- a general reporting-aware certificate theorem;
- additional Dafny cases;
- R3 real-world evidence;
- new Candidate B experiments;
- M4 work; and
- XAI work.

No current theorem or manuscript claim depends on these items.

## Future doctoral candidate queue

This ordered queue records research candidates, not promises or current claims.

### D1 — Frontier-obligation factorization

Question: Can current grouped exactness be decomposed into separately auditable
forward and reverse frontier obligations?

Gate: Pursue only if the factorization is operationally cheaper or more
auditable than checking full frontier equality directly.

### D2 — Weaker-than-atomic equivalence boundary

Question: What weakest structural or semantic conditions make pre-grouped
repair search extensionally equivalent to fine-grained repair followed by
post-hoc reporting?

### D3 — Incomplete-evidence assurance

Question: What guarantees remain valid when only part of the repair frontier is
enumerated or certified?

### D4 — Reporting-aware certificates

Question: What certificate evidence is sufficient for emitted-report
soundness, covered-region guarantees, or exact reportability?

These are research candidates, not promises and not current claims.

## Re-entry rule

No new M3 theorem should be started merely because it is mathematically
available. Reopen M3 theory only if at least one of the following holds:

1. advisor or reviewer feedback identifies a concrete insufficiency in the
   current theorem;
2. a prior-art result materially collapses the present novelty boundary;
3. one deferred theorem becomes necessary for a selected submission venue; or
4. the result is deliberately selected as a separate doctoral publication
   unit.

## Status-document synchronization

The public overview and canonical status summaries point to this freeze:

- `README.md`;
- `RESEARCH_STATUS.md`; and
- `docs/research_program_current.md`.

The Dafny pilot remains workflow evidence only and must not be confused with
M3 theorem evidence. Future theoretical strengthening is separate from the
current integrated paper.

## Repository consistency audit

The requested search covered `M3 pending`, `M3 integration pending`, `current
M3`, `FrontierSoundness`, `CRLift`, `ReverseLiftability`, `implementation
monotonicity`, `SatPhi monotonicity`, `atomicity`, `future`, `CPP 2027`, and
`submission-ready`.

| Classification | Relevant findings and disposition |
|---|---|
| `CURRENT_CORRECT` | `papers/cpp2027_m1_5_m3/`, `docs/m3_prior_art_claim_matrix.md`, and `docs/m3_manuscript_prior_art_sync_audit.md` state the current theorem and manuscript boundary correctly. Candidate B and paper README non-acceptance statements remain correct. |
| `HISTORICAL_KEEP` | `docs/m3_canonical_integration_precheck.md` contains pre-integration planning and the historical label “Implementation monotonicity,” while correctly stating that no theorem assumes `SatPhi` deletion monotonicity. It remains an identified historical audit and is not rewritten. |
| `STALE_UPDATE_REQUIRED` | The three canonical status documents previously said to continue M3 manuscript review/freeze work. They are updated by this canonicalization to point to the completed current-paper freeze and the submission-timing decision. |
| `FUTURE_NOT_CURRENT` | `FrontierSoundness`, `CRLift`, `ReverseLiftability`, `GC <-> FS ∧ CRLift`, weaker-than-atomic characterization, incomplete-evidence assurance, and reporting-aware certificates remain proposals only. M4 and XAI remain outside this task. |

Historical snapshots are retained when their date and role make the old state
unambiguous. This freeze does not rewrite unrelated M2 or M4 scientific status.

## Freeze gates

The canonicalization must retain the following verdicts:

```text
CURRENT_FUTURE_CONFLATION = 0
LEAN_THEOREM_MISMATCH = 0
SATPHI_MONOTONICITY_MISCLAIM = 0
NEW_THEOREMS = 0
NEW_EXPERIMENTS = 0
UNINTENDED_M2_M4_CHANGES = 0
```
