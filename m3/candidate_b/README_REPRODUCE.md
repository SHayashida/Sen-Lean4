# Candidate B M3 Application Evidence

> Candidate B is an artifact-defined M3-B instantiation under the declared bundled contract.

Evidence mode: `artifact-recomputed`.

This directory is the curated, hash-bound evidence freeze for the finite
Candidate B application. The package recomputes every reported family from the
frozen SAT/UNSAT status tables. It does not rerun the encoder or solver.

## Scientific question

Under the declared bundled contract, do the complete artifact-defined bundled
and split residual lattices satisfy ResidualFaithfulness, GroupSoundness, and
pointwise grouped correctness even though their raw repair families are not
canonical under representation change?

## Declared contract

- Contract atoms: `asymm`, `un`, `minlib`, `no_cycle4`.
- Implementation levers: `asymm`, `un`, `decisive_voter0`,
  `decisive_voter1`, `no_cycle4`.
- The `minlib` block contains both decisive-voter levers; all other blocks are
  singletons.
- Grouping is touch-any.
- `no_cycle3` is fixed inactive and is outside this application contract.

## One-command replay

Prerequisites are Python 3.9 or later using only the standard library and Lean
`leanprover/lean4:v4.15.0` for the focused theorem-core gate. The local freeze
used Python 3.9.6; CI uses Python 3.11. Exact environment fields are recorded
in `environment.json`. A new clone must run the repository's standard Lean
bootstrap (`lake exe cache get` and `lake build`) before the focused smoke gate.
The curated artifact rebuild itself uses only the Python standard library.

From the repository root, the default self-contained mode uses only tracked
files from the clean checkout:

```bash
./scripts/ci_m3_candidate_b.sh
```

The command verifies the package manifest, recomputes the 16 bundled and 32
split application rows, checks all 15 fault injections, and runs the focused
M3 Lean smoke/axiom audit. The full repository build remains available as
`lake build`.

To rebuild the curated evidence from the tracked evidence snapshot:

```bash
python3 m3/candidate_b/build_package.py
```

The default package builder is also self-contained:

```bash
python3 m3/candidate_b/build_package.py --source-mode curated
```

The optional provenance audit re-extracts the same whitelist from its recorded
historical Git object:

```bash
python3 m3/candidate_b/build_package.py --source-mode historical
```

Historical mode requires the recorded off-main source commit to be present
locally. Curated mode does not require that Git object because each copied file
is independently SHA-256- and Git-blob-bound in `source_artifacts.json` and
closed by `MANIFEST.sha256`.

The exact evidence source commit is
`1c2b9e7b979ba1a4b08c1d69f5400907cf2ca689`. The exact theorem-core source
commit, file blobs, declarations, smoke script, and allowed axiom set are bound
in `theorem_binding.json`.

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

Expected independently recomputed families are:

- raw: `{asymm}`, `{un}`, `{decisive_voter0}`, `{decisive_voter1}`,
  `{no_cycle4}`;
- grouped: `{asymm}`, `{un}`, `{minlib}`, `{no_cycle4}`;
- contract: `{asymm}`, `{un}`, `{minlib}`, `{no_cycle4}`.

Any missing row, unknown field, schema drift, hash mismatch, case-map mismatch,
or failed finite implication terminates with a non-zero exit. A failure means
the frozen artifact-defined claim is not reproduced; it does not diagnose the
social-choice semantics automatically.

No new solver run or UNSAT-proof replay is performed. The package trusts the
hash-bound SAT/UNSAT statuses only as artifact inputs, then independently
recomputes repair minimality, grouping, soundness, monotonicity, and exactness.

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

```bash
python3 m3/candidate_b/build_anonymous_package.py \
  --output /tmp/m3-candidate-b-anonymous.zip
```

The expected terminal verdict includes both:

```text
Raw repair canonicity: FAIL
Grouped contract-level correctness: PASS
```

Known limitations are the lack of semantic contract validation, encoder and
solver verification, proof replay, family-scale transfer, multi-scope evidence,
and an explicit repository redistribution license.
