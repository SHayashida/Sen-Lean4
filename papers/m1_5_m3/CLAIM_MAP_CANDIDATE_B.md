# Candidate B Claim Map

Status: frozen and mechanically checked.

The authoritative machine-readable map is `claim_map_candidate_b.json`. This
file records the human-readable audit and freeze verdict. The manuscript uses
the public term "bundled/split realization pair"; `Candidate B` remains an
internal artifact codename.

## Repository and evidence inventory

- Authoritative branch at start: `main`.
- Task branch: `codex/candidate-b-claim-freeze`.
- Starting commit: `bf8153b5a4d06c0be7507b1840d162b8c3123a0f`.
- Authoritative manuscript: `papers/m1_5_m3/main.tex`.
- Candidate B artifacts: `m3/candidate_b/`, the C1--C5 boundary in
  `papers/m1_5/CLAIM_BOUNDARY.md`, and `tools/check_cm_witness.py`.
- M3 theorem sources: `SocialChoiceAtlas/Reportability/{Defs,Atomic,GroupSound,Monotone,Examples}.lean`.
- Existing freeze/audit records: `m3/candidate_b/CLAIM_BOUNDARY.md`,
  `m3/candidate_b/README_REPRODUCE.md`, and the Candidate B documents under
  `docs/gates/`.
- Authoritative manuscript build: `make -C papers/m1_5_m3`.
- Focused application replay: `./scripts/ci_m3_candidate_b.sh`.

## Initial inventory scope

The inventory covers the title, abstract, introduction, contribution list,
claim-boundary discussion, concrete instance and no-go theorem, the
contract-level reading, theorem application, conclusion and limitations, data
availability statement, and artifact appendix. The title, related-work section,
and Lean correspondence table were reviewed and contain no Candidate B-specific
claim beyond records mapped elsewhere.

The pre-edit snapshot is retained per record as `initial_text` and
`initial_status`. The initial scan found 58 claims: 48 remain substantively
unchanged, six were weakened, and four received editorial-only changes. No
claim was deleted or merged.

The weakened records are CB-002, CB-007, CB-022, CB-025, CB-028, and CB-053.
They restore omitted M3 hypotheses or replace an unsupported normative/source-
theorem ambiguity reading with the supported finite reporting-granularity
statement. CB-026 is `EDITORIAL_ONLY`: it separates the C1--C5 solver replay
from the curated finite residual/group-soundness audit. CB-049 adds a short
running title to prevent header overlap; its scientific title is unchanged.
CB-033 and CB-034 restate the same exact singleton families compactly to keep
them within the review-mode column.

## Freeze mechanics

Every manuscript claim is enclosed by exactly one `% CLAIM: CB-*` / `% END
CLAIM: CB-*` pair. The checker binds the exact intervening TeX to SHA-256,
checks marker/map bijection, scans sentinel-bearing unmarked paragraphs against
an exact-hash reviewed exemption list, resolves JSON pointers and expected
values, resolves Lean symbols and repository-owned freeze commits, validates
the documented off-tree source SHA as a provenance identifier without requiring
that object in a clean clone, and verifies stored artifact hash bindings. It
also compares every refresh-derived classification, evidence mapping, scope,
and action with the canonical policy. Any wording or evidence drift fails
closed.

Run:

```bash
python3 tools/m1_5_m3/check_candidate_b_claim_map.py
```

`--refresh` is intentionally a deliberate audit action, not part of normal
builds.

## Claim accounting

```text
INITIAL_MANUSCRIPT_CLAIMS = 58
FINAL_MANUSCRIPT_CLAIMS = 58
UNCHANGED_CLAIMS = 48
WEAKENED_CLAIMS = 6
DELETED_CLAIMS = 0
MERGED_CLAIMS = 0
EDITORIAL_ONLY_CLAIMS = 4
SUPPORTED_COUNT = 58
UNSUPPORTED_COUNT = 0
OVERCLAIM_COUNT = 0
```

All mandatory non-claims are enumerated in the JSON map as `OUT_OF_SCOPE`,
including the absence of semantic/Lean Candidate B validation, organizational
validity, prevalence, family transfer, unconditional M3 necessity, raw-repair
canonicity, and any identification of the separate Dafny Case B evidence with
M3 GroupSoundness or exactness.

## Final gate

The authoritative build produced a visually inspected six-page PDF. Existing
non-fatal LaTeX/BibTeX and Lean linter warnings remain outside this editorial
freeze; all commands exited successfully.

```text
UNMAPPED_MANUSCRIPT_CLAIMS = 0
CLAIM_TEXT_HASH_MISMATCH = 0
EVIDENCE_REFERENCE_ERRORS = 0
UNACCOUNTED_DELETIONS = 0
OVERCLAIM = 0
UNSUPPORTED = 0
MANUSCRIPT_BUILD = PASS
CANDIDATE_B_CLAIM_FREEZE = PASS
```

The immutable freeze commit is reported after this state is committed. This
verdict must not be interpreted as a new Candidate B experiment, a new theorem,
or stronger semantic evidence.
