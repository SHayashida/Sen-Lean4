# Research Status

## Canonical state

- Last updated: 2026-08-19
- Branch: `main`
- Inspected GitHub `main` HEAD:
  `abec37c61a7c1217d8debf76b31366f1ff02e57f`.
- Current scientific baseline:
  `e33805d0ff0a64f12e450ba7aaa150729901d7d2`; the later Candidate B
  integration changes evidence/release engineering, not the scientific claim.
- Latest canonical theorem milestone: M3 finite-set reportability theorem core.
- Latest manuscript milestone: the former CPP 2027 draft is retained as a
  venue-neutral M1.5+M3 research draft under `papers/m1_5_m3/`; the CPP
  submission plan was discontinued on 2026-08-19.
- PR #14 completed the M2 reviewer audit.
- PR #16 completed canonical integration of the M3-A/B/C theorem core.
- PR #18 canonically bound the M1.5 C1-C5 witness claims to the deterministic
  checker and anonymous-supplement build workflow.
- PR #19 added the integrated CPP 2027 working draft.
- PR #21 integrated the validator-backed, self-contained Candidate B evidence
  package and resolved its clean-clone historical-object dependency.
- Candidate B evidence-freeze commit
  `99cba5cd45cadab283aab3784c9ff2180c8d8609` added the curated application
  package, independent validator, 15 fault injections, manifest, CI gate, and
  anonymous-package builder.

## Milestone status

| Milestone | Status | Canonical location |
|---|---|---|
| M1 | Complete in declared finite Sen24 scope | `main` |
| M1.5 | Raw repair non-canonicity established; C1-C5 witness binding canonical; venue-neutral integrated working draft present | `papers/m1_5/`, `tools/check_cm_witness.py`, PR #18/#19 |
| M2 | Semantic obstruction bridge complete, archived, and reviewer-audited `CONDITIONAL GO` | `main`, tag, GitHub Release, Zenodo DOI |
| M2.1 | Evidence partly canonical; paper integration deferred | PR #9 evidence |
| M3 | Abstract finite-set reportability theorem core canonical; integrated M1.5+M3 manuscript workspace present | `SocialChoiceAtlas/Reportability/`, `papers/m1_5_m3/` |
| Candidate B | Canonical validator-backed, artifact-defined M3-B application evidence package on `main`; no Lean or semantic upgrade | `m3/candidate_b/`, freeze commit `99cba5cd45cadab283aab3784c9ff2180c8d8609`, main integration `abec37c61a7c1217d8debf76b31366f1ff02e57f` |
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
  semantic contract validity, encoder correctness, solver correctness, or
  family-scale transfer.
- The canonical M1.5 checker validates only its narrower declared artifact
  claims; the separate Candidate B package freezes the full finite M3
  application without making it Lean-verified.
- The Dafny case is a minimum-example pilot. It does not validate M3 generally,
  establish practical prevalence, or decide which repair is normatively best.
- Fully active UNSAT remains an application-side assumption for impossibility
  repair interpretation, not a global theorem premise.
- The M4/Sen24 RC workspace does not establish Level C semantic-to-CNF
  correctness, Python/CNF correctness, checker formalization, or a new general
  Sen theorem.

Candidate B has a canonical validator-backed evidence package on `main`;
immutable release binding and redistribution review remain pending. It does
not establish semantic contract validity, encoder correctness, Candidate B
formalization in Lean, solver/proof replay, normative optimality, or
family-scale validity.

## Immediate main track

Maintain the canonical venue-neutral M1.5+M3 integrated research draft while
keeping its artifact-checked witness claims separate from its
Lean-kernel-checked abstract characterization. It has no current submission
target; any future venue requires a separate editorial and claim-map audit.

## Parallel tracks

- Maintain the frozen Candidate B package and review its future release gates
  without broadening the artifact-defined claim boundary.
- Extend the Dafny workflow pilot beyond one minimum example and identify the
  candidate consumers and report contracts used by verification engineers,
  repair-tool authors, and specification/API owners.
- Complete the required M2 major manuscript revision after its `CONDITIONAL GO`.
- Keep the XAI companion deferred or parallel without inferring a public status.

## Blocked or deferred

- Candidate B has no immutable tag or GitHub Release; external release remains
  gated by license and redistribution review.
- M2 submission remains gated by major revision.
- M2.1 manuscript integration is deferred.
- M4 institutional-warrant theorem development and publication are future work;
  the existing RC does not complete them.

## Next actions

1. Maintain the venue-neutral M1.5+M3 integrated research draft and frozen claim map.
2. Review the frozen Candidate B package for a future immutable release only
   after the license and redistribution gates are satisfied.
3. Expand the Dafny pilot to multiple cases and a real workflow before making
   external-validity or prevalence claims.
4. Complete the M2 major manuscript revision.
5. Keep the XAI companion deferred or parallel until public status is explicit.
6. Defer M4 institutional-warrant work from the immediate submission track.
