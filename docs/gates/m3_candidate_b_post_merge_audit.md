# Candidate B Post-Merge Audit

Date: 2026-07-22

## Canonical integration

- Pull request: #21
- Main integration commit: `abec37c61a7c1217d8debf76b31366f1ff02e57f`
- Evidence-freeze commit: `99cba5cd45cadab283aab3784c9ff2180c8d8609`
- Scientific source commit: `1c2b9e7b979ba1a4b08c1d69f5400907cf2ca689`
- Theorem-core/scientific baseline: `e33805d0ff0a64f12e450ba7aaa150729901d7d2`

The scientific source commit records historical provenance. The default
curated rebuild does not require that Git object.

## Bound identities on integrated main

| Item | Identity |
|---|---|
| Package builder Git blob | `0c1c8c7c859d48bfb298fe612b4bdb79f832ba9c` |
| Validator Git blob | `dc9f5ff93b107bfec3a1dfb35df6c7a5b6cedb58` |
| Theorem binding Git blob | `9237bdb04af0da2a8c38cd514ef18ba51b1e1248` |
| Evidence manifest Git blob | `76865fe36f9174fb3144340b81911540bf5cfc68` |
| Evidence manifest file SHA-256 | `9b677c5b016e073f8cd72f5515a77912497be2983d7d1ee594436ec271026e20` |
| Claim-boundary Git blob | `1ac94ae550cf7b8189f5b932a30735c1a1221987` |
| Anonymous archive SHA-256 | `e2ad1a31c3aaff1d4cc8a74ef4bcb44d6453b6615327678dae7aac569690d615` |
| Public release archive | `NOT CREATED` |

Two local post-merge anonymous builds and two builds in an independent remote
clean clone produced the same anonymous archive SHA-256. The archive was not
added to Git, uploaded, or released. The hash changed from the earlier branch
audit only because the fresh-runner smoke fix and the validator's bound smoke
hash changed; no theorem or scientific output changed.

## Verification

The following passed on integrated `main` and in a normal HTTPS clone of remote
`main`:

```bash
python3 m3/candidate_b/build_package.py
./scripts/ci_m3_candidate_b.sh
python3 -m unittest discover -s tools/m3_candidate_b/tests -v
python3 m3/candidate_b/verify_manifest.py
./scripts/ci_m3_smoke.sh
lake build
```

The remote clone was at the integration commit and did not contain the
historical scientific-source Git object. The curated builder, manifest,
validator, fault suite, focused theorem-core/axiom audit, and full Lean build
all passed. The working tree remained clean.

## Release boundary

The repository has no confirmed project-level redistribution license, and no
author approval to select one was provided. Therefore no
`RELEASE_BINDING.json`, annotated tag, GitHub Release, public release archive,
or historical source tag was created.

```text
REMOTE_INTEGRATION=PASS
LICENSE_GATE=BLOCKED
HISTORICAL_OBJECT_DEPENDENCY=ELIMINATED
IMMUTABLE_RELEASE_BINDING=BLOCKED
```

## Claim boundary

```text
Raw repair canonicity: FAIL
Artifact-defined grouped correctness: PASS
Candidate B Lean formalization: NOT CLAIMED
Semantic contract validity: NOT CLAIMED
Encoder correctness: NOT CLAIMED
Solver/proof replay: NOT CLAIMED
Normative optimality of grouping: NOT CLAIMED
Practical prevalence: NOT CLAIMED
Family-scale validity: NOT CLAIMED
```

Candidate B has a canonical validator-backed evidence package on `main`;
immutable release binding and redistribution review remain pending. It does
not establish semantic contract validity, encoder correctness, Candidate B
formalization in Lean, solver/proof replay, normative optimality, or
family-scale validity.
