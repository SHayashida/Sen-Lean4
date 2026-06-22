# M2 Zenodo Release Note

This file records the release flow for the M2 manuscript workspace.

## Current release

- Repository tag: `papers-m2-v2-obstruction-bridge`
- Git commit: `d7e5fd1ac94ab18330951b5d9741585dddc5b43a`
- GitHub release:
  `https://github.com/SHayashida/Sen-Lean4/releases/tag/papers-m2-v2-obstruction-bridge`
- Zenodo DOI (this version): `https://doi.org/10.5281/zenodo.20796920`
- Zenodo concept DOI: `https://doi.org/10.5281/zenodo.20468649`

Citation:

> Shunya Hayashida. (2026). SHayashida/Sen-Lean4: M2 finite semantic obstruction bridge (papers-m2-v2-obstruction-bridge). Zenodo. https://doi.org/10.5281/zenodo.20796920

This post-release documentation commit is not part of the tagged snapshot. The
tag `papers-m2-v2-obstruction-bridge` remains fixed at commit
`d7e5fd1ac94ab18330951b5d9741585dddc5b43a`.

## Previous release

- Repository tag: `papers-m2-v1`
- Git commit: `4feef8941801b1957847bb2fd6a965b57f83b863`
- Zenodo DOI (this version): `https://doi.org/10.5281/zenodo.20468650`
- GitHub release: `https://github.com/SHayashida/Sen-Lean4/releases/tag/papers-m2-v1`

## Release flow

1. Create a frozen Git tag for the manuscript state that will be archived.
2. Publish a GitHub release from that tag.
3. Let Zenodo archive the GitHub release and mint a DOI for the archived snapshot.
4. Record the minted DOI in post-release documentation without moving the tag.

## Manuscript insertion pattern

Use the version DOI in the paper as the stable archive reference, and keep the Git commit or tag nearby for source traceability. For future revisions, mint a new tag (for example `papers-m2-v2`) and let Zenodo issue a new version DOI; the concept DOI (if used) always resolves to the latest version.

## Scope

This note is specific to M2 and does not modify the M1 or M1.5 release policy.
