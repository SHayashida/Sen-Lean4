# Research Status

## Canonical state

- Last updated: 2026-07-21
- Branch: `main`
- Inspected GitHub `main` HEAD and current scientific/repository baseline:
  `e33805d0ff0a64f12e450ba7aaa150729901d7d2`
- Latest canonical theorem milestone: M3 finite-set reportability theorem core.
- Latest manuscript milestone: PR #19 integrated the M1.5+M3 CPP 2027 v1
  working draft under `papers/cpp2027_m1_5_m3/`.
- PR #14 completed the M2 reviewer audit.
- PR #16 completed canonical integration of the M3-A/B/C theorem core.
- PR #18 canonically bound the M1.5 C1-C5 witness claims to the deterministic
  checker and anonymous-supplement build workflow.
- PR #19 added the integrated CPP 2027 working draft.

## Milestone status

| Milestone | Status | Canonical location |
|---|---|---|
| M1 | Complete in declared finite Sen24 scope | `main` |
| M1.5 | Raw repair non-canonicity established; C1-C5 witness binding canonical; integrated CPP working draft present | `papers/m1_5/`, `tools/check_cm_witness.py`, PR #18/#19 |
| M2 | Semantic obstruction bridge complete, archived, and reviewer-audited `CONDITIONAL GO` | `main`, tag, GitHub Release, Zenodo DOI |
| M2.1 | Evidence partly canonical; paper integration deferred | PR #9 evidence |
| M3 | Abstract finite-set reportability theorem core canonical; integrated M1.5+M3 manuscript workspace present | `SocialChoiceAtlas/Reportability/`, `papers/cpp2027_m1_5_m3/` |
| Candidate B | Artifact-defined M3-B application; M1.5 witness claims are bound, but the full application evidence is not frozen canonically | pending curated M3 evidence package or immutable release binding |
| Dafny pilot | One public minimum example of formal-model-repair workflow choices | `SHayashida/dafny-m3-repair` at `208c2a59aa24fc1d2befe22842a7b07af8ced576` |
| XAI companion | Deferred or parallel; no public artifact status is claimed here | not found on the inspected Sen `main` branch |
| M4 | Future institutional-warrant track; repository-local Sen24 claim-boundary RC exists | `papers/m4/`; not the immediate publication track |

## Locked boundaries

- Arrow is excluded from the potential doctoral-scope candidate.
- The M2 semantic bridge is established.
- CNF/LRAT/atlas/repair family bridges are not claimed.
- O2/O3/O4 completeness does not imply minimality or uniqueness.
- The M3 core is abstract and contract-relative.
- Candidate B remains outside the M3 Lean core and is not a result about
  semantic contract validity.
- The canonical M1.5 checker validates only its declared artifact claims; it
  does not make Candidate B Lean-verified or freeze the full M3 application.
- The Dafny case is a minimum-example pilot. It does not validate M3 generally,
  establish practical prevalence, or decide which repair is normatively best.
- Fully active UNSAT remains an application-side assumption for impossibility
  repair interpretation, not a global theorem premise.
- The M4/Sen24 RC workspace does not establish Level C semantic-to-CNF
  correctness, Python/CNF correctness, checker formalization, or a new general
  Sen theorem.

## Immediate main track

Advance the canonical M1.5+M3 integrated CPP 2027 working draft while keeping
its artifact-checked witness claims separate from its Lean-kernel-checked
abstract characterization. The current v1 workspace is not represented as
accepted or submission-ready.

## Parallel tracks

- Canonicalize or freeze the Candidate B M3 application evidence without
  broadening its artifact-defined claim boundary.
- Extend the Dafny workflow pilot beyond one minimum example and identify the
  candidate consumers and report contracts used by verification engineers,
  repair-tool authors, and specification/API owners.
- Complete the required M2 major manuscript revision after its `CONDITIONAL GO`.
- Keep the XAI companion deferred or parallel without inferring a public status.

## Blocked or deferred

- Candidate B lacks a frozen canonical M3 evidence package or immutable release
  binding.
- M2 submission remains gated by major revision.
- M2.1 manuscript integration is deferred.
- M4 institutional-warrant theorem development and publication are future work;
  the existing RC does not complete them.

## Next actions

1. Continue the M1.5+M3 integrated CPP 2027 manuscript review and freeze work.
2. Freeze Candidate B application evidence through a curated package or
   immutable release binding.
3. Expand the Dafny pilot to multiple cases and a real workflow before making
   external-validity or prevalence claims.
4. Complete the M2 major manuscript revision.
5. Keep the XAI companion deferred or parallel until public status is explicit.
6. Defer M4 institutional-warrant work from the immediate submission track.
