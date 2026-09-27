# M1.5 Claim Boundary

This file is the paper-specific claim boundary for the M1.5 witness layer in
the venue-neutral M1.5+M3 integrated research draft. The former CPP 2027
submission plan was discontinued on 2026-08-19; historical archive and tag
identifiers below remain unchanged for reproducibility.

## Status

The following paper-level claims, C1-C5, are authorized for the M1.5 witness
layer only when they are bound to the anonymous supplementary archive
`cpp2027-anon-supplement.zip` and verified by the commands below.

This boundary deliberately separates two evidence layers:

- The M1.5 concrete witness is an artifact-level machine validation result.
- The M3 reportability theorem core is Lean-kernel checked under
  `SocialChoiceAtlas/Reportability/`.

The Candidate B / M1.5 concrete witness is not authorized as a Lean theorem.
This file does not broaden the claim boundary of the existing M1 manuscript
under `paper/`.

## Common Archive Binding

All artifact paths below are relative to the archive root
`cpp2027-anon-supplement/`.

Archive integrity command:

```bash
sha256sum -c MANIFEST.sha256
```

Witness verification command:

```bash
cd witness
python3 tools/check_cm_witness.py
```

`python-sat` is required for C2-C5. C1 uses only the Python standard library.

Archive-level files used by the claim boundary:

| Archive path | SHA-256 |
|---|---|
| `MANIFEST.sha256` | `7d03d31026a8717b1fbbb28457eddf0900c923830d39203e9f7cbe785eb03285` |
| `README_REPRODUCE.md` | `59cb6cab0c9fc77cc653077ffd97e3ba105b27a18b91f8821f854f127ee18ad1` |
| `witness/tools/check_cm_witness.py` | `ec402aa9af468eb825c8f1e21e18c91ef9949eb3deb8281ccb6e14d887124a4f` |
| `witness/artifacts/candidate_b_minlib_granularity/bundled/case_11101/sen24.manifest.json` | `09bff381123ae739d953f2a72b387503ff61ec00dbdfff863bbf03e7e813a88a` |
| `witness/artifacts/candidate_b_minlib_granularity/split/case_111101/sen24.manifest.json` | `9b6a812b8a1616121b19e93434eed759c40e0e60e68e4d2461d4275f31337414` |
| `witness/artifacts/candidate_b_minlib_granularity/comparison.json` | `0283c0cae11d5f6e7c5ef54dc6a10a1f909e458209294356b6c23d8bc307c23c` |

The generated CNFs are not stored in the anonymous archive. C1 binds the
regenerated CNFs to the archived manifests through the manifest field
`cnf_sha256`.

## Authorized Paper-Level Claims

| Claim | Authorized statement | Artifact binding | Verification |
|---|---|---|---|
| C1 | The bundled and split witness instances regenerate deterministically, have 6,936 variables and 36,290 clauses each, and are clause-multiset equivalent under the identity variable map. The checker sorts literals within each clause and compares the resulting clause multisets directly; it applies no nontrivial variable renaming. | Bundled manifest `witness/artifacts/candidate_b_minlib_granularity/bundled/case_11101/sen24.manifest.json` with `cnf_sha256 = 6570c79cdf3e5fb3235924793bdb53968470095ebd7dc19d8707c508d0fbe384`; split manifest `witness/artifacts/candidate_b_minlib_granularity/split/case_111101/sen24.manifest.json` with `cnf_sha256 = 35d24434bf66fbdf8f4ad0a734562b3527c665ad77e5e9c93594c1aae4e3b292`; checker `witness/tools/check_cm_witness.py`. | `sha256sum -c MANIFEST.sha256`; then `cd witness && python3 tools/check_cm_witness.py`, claim line `[PASS] C1`. |
| C2 | Both bundled and split full witness instances are UNSAT when re-solved through CaDiCaL via `python-sat`. | The same bundled and split manifests as C1, plus checker `witness/tools/check_cm_witness.py`. | `cd witness && python3 tools/check_cm_witness.py`, claim line `[PASS] C2`. |
| C3 | The bundled raw minimal repair family is exactly `{{asymm}, {un}, {minlib}, {no_cycle4}}`. | `witness/artifacts/candidate_b_minlib_granularity/comparison.json`, `repair_comparison[bundled_case_id = case_11101]`; checker re-solves all singleton deletions. | `cd witness && python3 tools/check_cm_witness.py`, claim line `[PASS] C3`. |
| C4 | The split raw minimal repair family is exactly `{{asymm}, {un}, {decisive_voter0}, {decisive_voter1}, {no_cycle4}}`. | `witness/artifacts/candidate_b_minlib_granularity/comparison.json`, `repair_comparison[split_case_id = case_111101]`; checker re-solves all singleton deletions. | `cd witness && python3 tools/check_cm_witness.py`, claim line `[PASS] C4`. |
| C5 | The transported bundled repair family differs from the split repair family: `{decisive_voter0, decisive_voter1}` is transported from `{minlib}` but is not inclusion-minimal on the split side. | Set-level consequence of C1-C4, re-derived explicitly by `witness/tools/check_cm_witness.py` using the same comparison and manifest artifacts. | `cd witness && python3 tools/check_cm_witness.py`, claim line `[PASS] C5`. |

No paper-level claim is authorized beyond C1-C5 by this file.

## Required Manuscript Fix Notes

The paper text must record the C1 strengthening precisely. In the M1.5
abstract, M1.5 Section 3 theorem statement and proof Step 2, the M1.5 appendix
description of the variable-renaming map, and Sections 2-3 of the M1.5+M3
integrated draft, replace "up to variable renaming" and
"designated variable-renaming map" with "under the identity variable map".

Reason: the checker compares sorted literal clauses by direct `Counter`
equality and applies no nontrivial renaming. Therefore the concrete witness
establishes clause-multiset equivalence under the identity variable map, which
is stronger than equivalence under an unspecified renaming.

## Private Metadata and Historical Submission Freeze

The following metadata may be recorded in this public repository claim-boundary
file, but it must not be included in the anonymous supplementary archive:

- Witness artifact source: file-level extraction from off-main source SHA
  `1c2b9e7b979ba1a4b08c1d69f5400907cf2ca689`; no cherry-pick is claimed here.
- Lean source: canonical `main` containing the Reportability core.
- Historical provisional submission tag: `papers-m1_5-m3-cpp2027-submission`;
  it was never finalized and must not be presented as an active target.
- Archive anonymity rule: names, affiliations, GitHub URLs, Codex branch names,
  Zenodo/SSRN identifiers, private absolute paths, and local workflow metadata
  must remain outside `cpp2027-anon-supplement.zip`.
- Any future publication or public artifact release requires a new target,
  explicit review, and updated archival identifiers.

## Local Verification Record

G1 local verification on 2026-07-05:

- Repository `lake exe cache get`: PASS.
- Repository `lake build`: PASS with existing non-fatal linter warnings.
- Repository `grep -rnE '\bsorry\b|\badmit\b' SocialChoiceAtlas/Reportability/ || true`: no hits.
- Supplement `sha256sum -c MANIFEST.sha256`: PASS.
- Supplement `python3 tools/check_cm_witness.py`: PASS for C1-C5 after
  installing `python-sat` in a temporary environment.
- Supplement `lake exe cache get`: PASS.
- Supplement `lake build`: PASS with existing non-fatal linter warnings.
- Supplement Reportability `sorry` / `admit` grep: no hits.
