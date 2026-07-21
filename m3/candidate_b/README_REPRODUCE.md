# Candidate B M3 Application Evidence

> Candidate B is an artifact-defined M3-B instantiation under the declared bundled contract.

This directory is the curated, hash-bound evidence freeze for the finite
Candidate B application. The package recomputes every reported family from the
frozen SAT/UNSAT status tables. It does not rerun the encoder or solver.

## Declared contract

- Contract atoms: `asymm`, `un`, `minlib`, `no_cycle4`.
- Implementation levers: `asymm`, `un`, `decisive_voter0`,
  `decisive_voter1`, `no_cycle4`.
- The `minlib` block contains both decisive-voter levers; all other blocks are
  singletons.
- Grouping is touch-any.
- `no_cycle3` is fixed inactive and is outside this application contract.

## One-command replay

From the repository root:

```bash
./scripts/ci_m3_candidate_b.sh
```

The command verifies the package manifest, recomputes the 16 bundled and 32
split application rows, checks all 15 fault injections, and runs the focused
M3 Lean smoke/axiom audit. The full repository build remains available as
`lake build`.

To rebuild the curated evidence from its exact historical Git source object:

```bash
python3 m3/candidate_b/build_package.py
```

That stricter builder requires the recorded off-main source commit to be
present locally. Ordinary package replay does not require that historical Git
object because each copied file is independently SHA-256- and Git-blob-bound
in `source_artifacts.json` and closed by `MANIFEST.sha256`.

## Evidence coverage

- residual faithfulness: 16/16 block-aligned rows, zero mismatches;
- contract repairs: all 16 contract deletions;
- raw repairs: all 32 implementation deletions;
- direct GroupSoundness: all 32 implications, zero violations;
- deletion monotonicity: all 81 comparable contract pairs, zero violations;
- pointwise grouped correctness: all 16 contract deletions, zero mismatches;
- fault injection: 15/15 mandatory corruptions rejected.

Raw repairs are not canonical under the bundled representation. The validated
grouped result is only the finite artifact-defined result under this declared
contract.

## Package map

- `contract.json`: exact contract, block map, grouping, and evidence mode.
- `case_schema.json`: bit order, mask semantics, and inactive-atom filter.
- `source_artifacts.json`: exact source commit/path/blob/content binding.
- `theorem_binding.json`: exact M3 theorem-core files, declarations, smoke
  gate, and axiom audit; it explicitly records that Candidate B is not
  formalized in Lean.
- `evidence/`: whitelist-only source tables and per-case manifests/summaries.
- `generated/`: independently recomputed JSON/Markdown audit outputs.
- `MANIFEST.sha256`: exact package closure.
- `CLAIM_BOUNDARY.md`: allowed claims and mandatory non-claims.
- `LICENSE_STATUS.md`: redistribution/release caveat.

The anonymous package must be built separately with
`build_anonymous_package.py`; the public package is never renamed and reused as
an anonymous archive.
