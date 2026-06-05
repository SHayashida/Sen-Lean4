# M2 Zenodo Release Note

This file records the release flow for the M2 manuscript workspace.

## Current release

- Repository tag: `papers-m2-v1`
- Git commit: `4feef8941801b1957847bb2fd6a965b57f83b863`
- Zenodo DOI (this version): `https://doi.org/10.5281/zenodo.20468650`
- GitHub release: `https://github.com/SHayashida/Sen-Lean4/releases/tag/papers-m2-v1`

Citation:

> Shunya Hayashida. (2026). SHayashida/Sen-Lean4: M2 submission snapshot (papers-m2-v1). Zenodo. https://doi.org/10.5281/zenodo.20468650

## Release flow

1. Create a frozen Git tag for the manuscript state that will be archived.
2. Publish a GitHub release from that tag.
3. Let Zenodo archive the GitHub release and mint a DOI for the archived snapshot.
4. Insert the minted DOI into the manuscript and the reproducibility note.

## Manuscript insertion pattern

Use the version DOI in the paper as the stable archive reference, and keep the Git commit or tag nearby for source traceability. For future revisions, mint a new tag (for example `papers-m2-v2`) and let Zenodo issue a new version DOI; the concept DOI (if used) always resolves to the latest version.

## Scope

This note is specific to M2 and does not modify the M1 or M1.5 release policy.
