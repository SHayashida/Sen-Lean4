# Candidate B License and Provenance Audit

Date: 2026-07-22

This is a repository evidence audit, not legal advice. It distinguishes public
visibility, observed copyright/license notices, provenance evidence, and
permission to redistribute a GitHub Release asset.

## 1. Repository license state

The inspected tree contains no root or project-level `LICENSE`, `LICENSE.md`,
`LICENSE.txt`, `COPYING`, `COPYRIGHT`, `NOTICE`, `THIRD_PARTY_NOTICES`, or
`CITATION.cff`.

Several older Lean files contain headers saying that Apache-2.0 terms are
described in `LICENSE`, but that referenced file is absent. The M3
`SocialChoiceAtlas/Reportability/` files copied into the anonymous package do
not contain file-level license headers. These observations do not establish a
repository-wide license or a release redistribution grant.

No license was selected, inferred, or committed. Author approval for a license
decision has not been provided in this task.

## 2. Provenance categories

| Category | Candidate B content | Current status |
|---|---|---|
| A. Author-created source | Validator, tests, builders, schemas, documentation, metadata | `AUTHOR_CONFIRMATION_REQUIRED` |
| B. Author-created research outputs | Historical evidence snapshot and recomputed audit outputs | `AUTHOR_CONFIRMATION_REQUIRED` |
| C. Third-party executable/source | Lean/mathlib/Python dependencies; not vendored into the package | `EXCLUDE_FROM_RELEASE` |
| D. Third-party templates/publication files | LaTeX classes, styles, fonts, logos; not included | `EXCLUDE_FROM_RELEASE` |
| E. Generated proof/certificate artifacts | No CNF, LRAT, proof log, model, solver log, or binary included | `EXCLUDE_FROM_RELEASE` |
| F. Unclear provenance | M3 Lean source copies included by the anonymous builder | `AUTHOR_CONFIRMATION_REQUIRED` |

The machine-readable inventory is
`m3/candidate_b/REDISTRIBUTION_INVENTORY.json`. It records each file class,
origin, evidence source, canonical/anonymous inclusion, release status, and
required action.

## 3. Candidate package findings

The canonical tracked package contains source code, documentation, JSON
schemas and metadata, 99 exact historical evidence files, and deterministic
validator outputs. It contains no third-party binary, SAT solver, CNF, LRAT,
proof log, model, PDF, publication template, font, or logo.

The generated anonymous archive additionally copies four M3 Lean source files,
the focused smoke script, and `lean-toolchain`. Their content hashes are bound,
but redistribution terms remain unresolved.

The evidence files have strong technical provenance through exact Git source
paths, Git blob IDs, and SHA-256 hashes. Technical provenance does not itself
grant redistribution permission.

## 4. Minimum publication policy

Allowed without making a licensing claim:

- push and review source on the existing public repository;
- merge the validator-backed package into `main`;
- run local and CI reproduction;
- describe the package as publicly viewable and canonically tracked.

Not authorized by this audit:

- describing the repository or artifact as open source, freely reusable, or
  permissively licensed;
- publishing a Candidate B GitHub Release archive;
- asserting that anonymous-supplement redistribution is permitted;
- selecting MIT, Apache-2.0, BSD-3-Clause, CC BY, CC0, or any other license on
  behalf of the copyright holder.

## 5. Required resolution

Before an immutable Candidate B Release, the copyright holder must explicitly:

1. confirm ownership or authority for the Candidate B code, documentation,
   research outputs, and M3 Lean files;
2. select terms for source code, documents/manuscript material, and research
   data/artifacts;
3. decide whether the anonymous archive may redistribute the M3 Lean source;
4. supply required notices or exclude unresolved files from the Release;
5. approve the final public asset whitelist.

## 6. Verdict

```text
LICENSE_GATE=BLOCKED
AUTHOR_APPROVAL=NOT PROVIDED
RELEASE_ASSET_POLICY=NO CANDIDATE B ASSETS AUTHORIZED
```

This gate does not alter the scientific audit verdict. It blocks Gate D tag and
GitHub Release creation until an explicit rights decision is recorded.
