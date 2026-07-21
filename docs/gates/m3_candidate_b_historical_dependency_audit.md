# Candidate B Historical-Object Dependency Audit

Date: 2026-07-22

## 1. Prior dependency

The original `m3/candidate_b/build_package.py` always extracted the 99-file
whitelist from off-main source commit
`1c2b9e7b979ba1a4b08c1d69f5400907cf2ca689`. Validation from a clean exported
tree worked, but strict package rebuilding failed when that Git object was not
present.

## 2. Remediation

The builder now exposes two explicit modes:

```bash
python3 m3/candidate_b/build_package.py --source-mode curated
python3 m3/candidate_b/build_package.py --source-mode historical
```

`curated` is the default. It validates and rebuilds deterministic outputs from
the tracked, whitelist-closed evidence snapshot and its SHA-256/Git-blob source
binding. It does not invoke Git or require an off-main object.

`historical` retains the stricter provenance audit. It re-extracts every
whitelisted file from the exact recorded source commit, recreates
`source_artifacts.json`, verifies the source commit/path/blob relationship, and
then runs the same validator and fault suite.

## 3. Mode-equivalence gate

The two modes were run consecutively in the repository containing the
historical object. The following independently generated outputs were compared:

- residual status table and fully active verdicts;
- ContractRepair;
- RawRepair and raw non-canonicity;
- GroupedRepair;
- direct GroupSoundness and triangulation;
- PsiDeletionMonotonicity;
- pointwise grouped correctness;
- overall audit verdict;
- fault-injection results;
- source evidence bytes and source-artifact binding.

All compared outputs were byte-identical. Archive hashes may change when
documentation or the redistribution inventory changes; no scientific output
difference was observed between source modes.

## 4. Clean-clone requirement

The remote clean-clone test must clone the public repository normally, check
out the Candidate B branch or integrated `main`, and run:

```bash
python3 m3/candidate_b/build_package.py --source-mode curated
./scripts/ci_m3_candidate_b.sh
python3 m3/candidate_b/verify_manifest.py
```

It must not use a local repository URL, alternate object database, manual
`.git/objects` copy, source-tree path, or local-only branch.

This gate was executed from a normal HTTPS clone of the remote Candidate B
branch. The clone did not contain
`1c2b9e7b979ba1a4b08c1d69f5400907cf2ca689`. The curated builder and manifest
verification passed before any Lean dependency setup. After the standard Lean
bootstrap (`lake exe cache get` followed by `lake build`), the complete
`ci_m3_candidate_b.sh` gate passed. The focused smoke gate relies on repository
`.olean` files produced by that standard bootstrap; this is a Lean build
prerequisite, not a historical-source-object dependency.

## 5. Historical tag decision

No historical source tag was created. A proposed
`m3-candidate-b-source-v1` tag would expose the complete source commit and is
not authorized while `LICENSE_GATE=BLOCKED`. The curated snapshot preserves
the required evidence and provenance hashes without making that tag necessary
for ordinary reproduction.

## 6. Verdict

```text
CURATED_MODE=PASS
HISTORICAL_MODE=RETAINED_FOR_PROVENANCE
SCIENTIFIC_OUTPUT_EQUIVALENCE=PASS
REMOTE_CLEAN_CLONE=PASS
HISTORICAL_OBJECT_CONFIRMED_ABSENT=PASS
HISTORICAL_OBJECT_DEPENDENCY=ELIMINATED
HISTORICAL_SOURCE_TAG=NOT CREATED
```
