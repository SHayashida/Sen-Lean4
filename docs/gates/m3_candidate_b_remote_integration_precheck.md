# Candidate B Remote Integration Precheck

Date: 2026-07-22

Purpose: determine whether the local Candidate B evidence-freeze branch may be
pushed and opened as a public integration pull request without changing the
scientific claim boundary.

> Candidate B is an artifact-defined M3-B instantiation under the declared bundled contract.

## 1. Git and GitHub state

| Item | Inspected value |
|---|---|
| Local branch | `codex/m3-candidate-b-evidence-freeze` |
| Inspected local HEAD before this precheck commit | `27b9e059b7a23303e65ef8418853acf19205b42a` |
| `origin/main` | `e33805d0ff0a64f12e450ba7aaa150729901d7d2` |
| Merge base | `e33805d0ff0a64f12e450ba7aaa150729901d7d2` |
| Ahead/behind before this commit | ahead 8, behind 0 |
| Remote Candidate B branch | Not found |
| Existing Candidate B PR | Not found |
| Repository visibility | Public |
| Default branch | `main` |
| Candidate B tag or Release | Not found |
| Working tree before the privacy-token correction | Clean |

The branch preserves the existing commit sequence. No rebase, squash,
force-push, tag move, or history rewrite was performed.

## 2. Commit and content audit

The branch contains the earlier public-status synchronization followed by the
freeze protocol, validator, fault tests, curated package, documentation
binding, whitespace normalization, and a scanner self-match correction. The
commits remain responsibility-separated. No existing Lean theorem, encoder,
solver result, protected certificate, tag, Release, or DOI was changed.

The commit author name and placeholder email are present only in normal Git
commit metadata. No added file contains a local absolute path, email address,
private note, or machine hostname.

Content checks:

- no tracked ZIP, tar archive, PDF, image, executable binary, or solver binary
  was added by the branch;
- the largest added Candidate B file is the tracked split atlas JSON at 68,605
  bytes;
- executable bits are limited to the intended Python builders/verifiers and
  shell CI gate;
- ignored build outputs, local result trees, private notes, and editor/OS files
  remain untracked;
- the curated package excludes TruthWeave, XAI, M4, `.git`, `.lake`, caches,
  and unrelated result trees.

The initial absolute-path scan matched only the scanner's own `/Users/`
detection token. Commit `27b9e059b7a23303e65ef8418853acf19205b42a`
preserves the runtime check while removing the literal self-match. The repeated
scan then returned no branch-content finding.

## 3. Freeze validation

| Gate | Result |
|---|---|
| Historical-source package build | PASS; 99-file whitelist and source binding |
| Candidate B validator | PASS; `artifact-recomputed` |
| Fault injections | PASS; 15/15 rejected at expected gates |
| Package manifest | PASS; 136 files |
| ResidualFaithfulness | PASS; 16/16, zero mismatches |
| Direct GroupSoundness | PASS; 32/32, zero violations |
| Deletion monotonicity | PASS; 81 comparable pairs, zero violations |
| Pointwise grouped correctness | PASS; 16/16, zero mismatches |
| Focused M3 smoke and axiom audit | PASS |
| Full `lake build` | PASS with existing linter warnings only |
| Anonymous validator and identity scan | PASS |
| Anonymous deterministic rebuild | PASS; identical two-run SHA-256 |
| `git diff --check origin/main..HEAD` | PASS |
| Markdown path/link scan | PASS |
| Forbidden positive-overclaim scan | PASS |
| Stale-language scan | PASS |
| Generated archive tracked | No |

Anonymous pre-push archive SHA-256:

```text
8cf6605a2a0891847b3a458ee727d9ec6f9abb4e67653e09fbf7d671f0c92470
```

Commands executed successfully:

```bash
python3 m3/candidate_b/build_package.py
./scripts/ci_m3_candidate_b.sh
python3 -m unittest discover -s tools/m3_candidate_b/tests -v
python3 m3/candidate_b/verify_manifest.py
./scripts/ci_m3_smoke.sh
lake build
python3 m3/candidate_b/build_anonymous_package.py --output <temporary-archive>
git diff --check origin/main..HEAD
```

## 4. License and provenance precondition

No repository-level `LICENSE`, `COPYING`, `NOTICE`,
`THIRD_PARTY_NOTICES`, or `CITATION.cff` was found. Several older Lean files
refer to an Apache-2.0 `LICENSE` file that is absent from the inspected tree;
those headers do not resolve repository-wide or package redistribution terms.

The package can be pushed and reviewed on the public repository, but no public
archive Release, open-source status, or reuse permission may be asserted until
the separate provenance inventory is complete and the copyright holder makes
an explicit license decision.

## 5. Pre-push verdict

```text
REMOTE_PUSH_READINESS=PASS
PR_CREATION_READINESS=PASS
LICENSE_GATE=PENDING_DETAILED_AUDIT
HISTORICAL_OBJECT_DEPENDENCY=DOCUMENTED_BUT_RETAINED
IMMUTABLE_RELEASE_BINDING=BLOCKED
```

The branch may be pushed and a pull request may be opened. Release engineering
must stop before tag or GitHub Release creation unless the license and
historical-dependency gates are resolved.
