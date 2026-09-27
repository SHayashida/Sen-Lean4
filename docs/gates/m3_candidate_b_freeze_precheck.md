# Candidate B M3 Evidence-Freeze Precheck

## Decision

**GO**, subject to the fail-closed gates defined below.

The required bundled and split residual lattices are reachable as immutable Git
objects, their bit orders are explicit in the source atlases, and the canonical
M3 theorem core is present on `main`. The evidence package must extract inputs
from the recorded Git source commit rather than from the ignored local
`results/` tree.

This precheck authorizes an artifact-defined evidence freeze only. It does not
authorize any semantic, encoder-correctness, solver-correctness, or Lean
formalization claim for Candidate B.

Required wording:

> Candidate B is an artifact-defined M3-B instantiation under the declared
> bundled contract.

## 1. Git state inspected

Inspection date: 2026-07-21.

| Item | Inspected value |
|---|---|
| Working branch | `codex/m3-candidate-b-evidence-freeze` |
| Branch HEAD at precheck | `88270e89f241e476cd149ace1996ca78bfb070f7` |
| Current `origin/main` HEAD | `e33805d0ff0a64f12e450ba7aaa150729901d7d2` |
| Merge base with `origin/main` | `e33805d0ff0a64f12e450ba7aaa150729901d7d2` |
| Working tree | Clean before this precheck file was added |
| Branch relationship | One existing docs-only status-sync commit above `origin/main` |
| M1.5 evidence-binding merge | `5b9b4af226a2a5390fa618e45caeab3121831988` |
| Deterministic M1.5 checker | `1cf11e8c82d89a0ebf8a266323322f2cb6806a0d` |
| Anonymous supplement builder | `ee31467019e35034434174d3bac9ca83d6eb1bee` |
| M1.5 claim-boundary binding | `6f59a24109dc93ec7e59038ad28f0313b8c9eccd` |
| M3 theorem-core integration | `be4132ba3b6f8168b75644e0928d7b2609048049` |
| CPP manuscript integration / `main` HEAD | `e33805d0ff0a64f12e450ba7aaa150729901d7d2` |
| Candidate B evidence source commit | `1c2b9e7b979ba1a4b08c1d69f5400907cf2ca689` |
| Evidence publication commit in source history | `5d1e29ff288e00ed6a0f2cf4b590511dfbf58256` |

Relevant branches found include:

- `origin/codex/candidate-b-minlib-granularity`;
- `origin/codex/m2.1-candidate-b`;
- `origin/codex/m3-lean-reportability`;
- `origin/codex/m3-paper-scaffold`;
- the canonical M3 integration branches and the CPP integration branches.

The exact evidence source commit is reachable from
`origin/codex/m3-lean-reportability` and `origin/codex/m3-paper-scaffold`. It is
not contained in a release tag.

Relevant tags inspected:

| Tag | Peeled commit | Candidate B freeze binding |
|---|---|---|
| `papers-m2-v1` | `4feef8941801b1957847bb2fd6a965b57f83b863` | None |
| `papers-m2-v2-obstruction-bridge` | `d7e5fd1ac94ab18330951b5d9741585dddc5b43a` | None |
| `papers-m4-v0.1-rc1` | `706d7cb9ed8f4b2066bb66e91ae7691f3b2b6ec0` | None |

The GitHub release query returned only the two M2 releases. No Candidate B or
M3 evidence release was found. No Candidate B evidence DOI binding is recorded
in the inspected repository state.

## 2. Required-path inspection

### Canonical on `main`

- `papers/m1_5/`;
- `papers/m1_5_m3/`;
- `SocialChoiceAtlas/Reportability/Defs.lean`;
- `SocialChoiceAtlas/Reportability/Atomic.lean`;
- `SocialChoiceAtlas/Reportability/GroupSound.lean`;
- `SocialChoiceAtlas/Reportability/Monotone.lean`;
- `SocialChoiceAtlas/Reportability/Examples.lean`;
- `scripts/ci_m3_smoke.sh`;
- `tools/check_cm_witness.py`;
- `tools/build_anon_supplement.py`;
- `papers/m1_5/CLAIM_BOUNDARY.md`.

### Reachable only through the recorded off-main source commit

- `docs/m3_candidate_b_group_soundness_audit_plan.md`;
- `docs/m3_candidate_b_group_soundness_audit_result.md`;
- `results/20260401/candidate_b_minlib_granularity/comparison.json`;
- `results/20260401/candidate_b_minlib_granularity/comparison.csv`;
- the 32-case bundled atlas and per-case summaries/manifests;
- the 64-case split atlas and per-case summaries/manifests;
- the Candidate B human-readable source summary.

### Generated but untracked locally

An ignored `results/20260401/candidate_b_minlib_granularity/` tree is present
in the working directory. `git ls-files` reports zero tracked files for this
tree at the current HEAD. It is not an admissible freeze input. The package
builder must extract the exact whitelisted blobs from the recorded source
commit.

### Missing before implementation

- a canonical `m3/candidate_b/` evidence package;
- a dedicated independent M3 Candidate B validator;
- machine-readable contract and case schemas;
- direct full-lattice GroupSoundness and pointwise exactness outputs;
- fault-injection tests;
- a package manifest and deterministic public/anonymous builders;
- an immutable Candidate B release identity.

### Stale or superseded as a verdict source

The off-main group-soundness audit result is retained as provenance, but it is
not sufficient for the freeze verdict. It reads precomputed repair-family
fields and derives RawRepair completeness and unrestricted GroupSoundness by
inference. The new validator must independently recompute all minimal families,
all 32 GroupSoundness implications, all bundled monotonicity pairs, and all 16
pointwise correctness values.

## 3. Source artifact shape

The source `comparison.json` records:

- bundled universe:
  `[asymm, un, minlib, no_cycle3, no_cycle4]`;
- split universe:
  `[asymm, un, decisive_voter0, decisive_voter1, no_cycle3, no_cycle4]`;
- 32 block-mapped rows across the full five-atom bundled universe;
- exact clause-multiset and status equality fields, which may be cross-checks
  but not trusted verdict inputs.

The source atlases record:

| Representation | Bit order | Cases | Status counts |
|---|---|---:|---|
| Bundled | `[asymm, un, minlib, no_cycle3, no_cycle4]` | 32 | 30 SAT / 2 UNSAT |
| Split | `[asymm, un, decisive_voter0, decisive_voter1, no_cycle3, no_cycle4]` | 64 | 62 SAT / 2 UNSAT |

Each atlas row includes `case_id`, `mask_bits`, `mask_int`, `axioms_on`,
`axioms_off`, solver status, and embedded manifest metadata. Per-case
`summary.json` and `sen24.manifest.json` files provide independent hash-bound
cross-check inputs.

For the declared M3 application, `no_cycle3` is fixed inactive. This yields:

- exactly 16 bundled contract residuals over
  `{asymm, un, minlib, no_cycle4}`;
- exactly 32 split implementation residuals over
  `{asymm, un, decisive_voter0, decisive_voter1, no_cycle4}`.

The fully active application rows are `case_11101` and `case_111101`; both are
recorded UNSAT. Their recorded CNF hashes are respectively:

- `6570c79cdf3e5fb3235924793bdb53968470095ebd7dc19d8707c508d0fbe384`;
- `35d24434bf66fbdf8f4ad0a734562b3527c665ad77e5e9c93594c1aae4e3b292`.

## 4. Canonical theorem-core binding inputs

The package will bind to `origin/main` commit
`e33805d0ff0a64f12e450ba7aaa150729901d7d2` and the following Git blob IDs:

| Lean file | Blob ID |
|---|---|
| `SocialChoiceAtlas/Reportability/Defs.lean` | `03053943a8f2429c79340734a23b0b0609058e9b` |
| `SocialChoiceAtlas/Reportability/GroupSound.lean` | `2ef41b003d63088bc762a493c6ed1590d2996293` |
| `SocialChoiceAtlas/Reportability/Monotone.lean` | `37958d0c63c835365a8dda94ec615f7e5ff719f4` |
| `SocialChoiceAtlas/Reportability/Examples.lean` | `14ce4b823795056f9cb91814acf83fb1b4fedcbe` |

Bound declaration names:

- `m3b_grouped_correctness`;
- `m3b_two_realization`;
- `m3c_converse`;
- `groupSoundness_iff`;
- `audit_cost_collapse`.

The focused gate audits the expected axiom set
`[propext, Classical.choice, Quot.sound]`. Candidate B data are not imported by
these Lean modules.

## 5. Evidence classification

| Artifact | Classification before freeze | Freeze treatment |
|---|---|---|
| M3 Lean theorem core | Canonical on `main` | Bind commit, blobs, declarations, and smoke result |
| M1.5 checker and claim boundary | Canonical on `main` | Provenance and cross-check only |
| Existing anonymous supplement builder | Canonical on `main` | Design precedent; not the Candidate B freeze builder |
| Candidate B comparison and atlases | Off-main, Git-object reachable | Curate exact whitelisted blobs |
| Per-case summaries/manifests | Off-main, Git-object reachable | Curate all rows needed for 16/32 lattice checks |
| Existing M3 Candidate B audit prose | Off-main and inference-based | Provenance only; never trusted as a verdict |
| Ignored local result tree | Generated/untracked/local-only | Reject as a builder input |
| Candidate B release/tag/DOI | Missing | Propose identity only after all gates pass |

## 6. Stop-condition audit

| Stop condition | Precheck result |
|---|---|
| Required 16-row artifact missing | Clear: all rows are present in Git objects |
| Split 32-row application lattice unavailable | Clear: extractable from the 64-row split atlas |
| Case-bit order ambiguous | Clear: explicit ordered universes and row fields agree |
| Source hashes unavailable | Clear: Git blob IDs and embedded CNF hashes are available |
| Bundled/split mapped status contradiction | Clear at precheck; validator must recompute |
| Raw repair family cannot be recomputed | Clear: full retained-set lattices are present |
| `no_cycle3` state ambiguous | Clear: dedicated bit and active/off fields are explicit |
| Theorem-core binding unknown | Clear: commit, blobs, declarations, and gate exist |
| Private data in source set | Not yet cleared; builder identity scan is mandatory |
| Redistribution/license status | Not yet cleared; package must record repository license findings and limit itself to repository-owned text/JSON evidence |
| Fault injection undetected | Not yet cleared; mandatory before freeze verdict |

Implementation must produce `INCOMPLETE` or a non-zero exit if any unresolved
gate cannot be cleared. A PASS package may be declared only after the curated
copy, independent recomputation, fault-injection suite, manifest verification,
Lean gate, and anonymous scan all pass.
