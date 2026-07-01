# M4 v0.1 Reproducibility Evidence Note

## 1. Repository state

Repository: `SHayashida/Sen-Lean4`.

Branch at the start of this pass: `codex/m4-repair-orbit-precheck`.

Pre-edit `git status --short`:

```text
 M papers/README.md
```

The working tree was not clean before this pass. The pre-existing change was
outside the allowed M4 files for this task and was left unstaged/unmodified.
Because the tree was already dirty, this pass should not be treated as a clean
release binding unless the final release commit or tag is created after
reviewing all uncommitted changes.

Pre-edit `git diff --check`: passed.

Manual claim-boundary check after this pass: passed. The manuscript still does
not claim Python encoder correctness, `_right_clauses` correctness,
SAT/CNF artifact correctness, semantic-to-CNF correctness, full selector-free
equivalence to Lean `MINLIB`, a whole-certificate Lean verification, a
structural proof of the Mask-Shape Collapse Law, a new general Sen theorem, a
family-scale lift, or an AI governance/alignment solution.

## 2. Bound commit

Pre-pass `HEAD`:

```text
e393e5615410f56390a166421060611d0e16267a
```

Commit message:

```text
docs(m4): resolve v0.1 release blockers
```

This commit is the starting point for the reproducibility hardening pass. If
these reproducibility edits are committed, the public v0.1 release binding
should cite the post-task commit or release tag, not the pre-task commit above.

## 3. Lean bridge compilation

Smallest Lean bridge check run in this pass:

```text
lake env lean SocialChoiceAtlas/Sen/RightAtomBridge.lean
```

Result: exit status `0`.

The command emitted no stdout or stderr on successful compilation. The tracked
log is:

```text
papers/m4/repro/right_atom_bridge_lean_check.log
```

This check compiles the Lean bridge source. It does not modify Lean files, does
not check generated CNF/LRAT artifacts, and does not establish Python/CNF or
semantic-to-CNF correctness.

## 4. M4 checker / finite-audit evidence

The required command search was run before editing:

```text
grep -R "m4\|mask\|shape\|phase\|certificate\|checker\|RepairEmpty\|orbit\|fiber\|truncation\|mixedness" -n docs scripts papers/m4 | head -200
```

Additional targeted searches inspected M4 result docs and
`scripts/exploration/m4/` for Certificate 1, mask-shape audit, and Certificate
2 checker entry points.

Initial result: documented command not found for a safe 48-cell finite-audit
checker rerun in the inspected result documents. The repository contains
relevant M4 scripts, including:

```text
scripts/exploration/m4/residual_class_coverage_certificate.py
scripts/exploration/m4/mask_shape_collapse_law_audit.py
scripts/exploration/m4/certificate2_phase_diagram_checker.py
```

The result documents inspected for the first release note recorded inputs,
outputs, and PASS verdicts rather than a release-bound shell command. A later
reproducibility pass classified this as Case B: no single documented command,
but an existing three-stage script pipeline was clear enough to replay safely
without changing checker logic. The replay is recorded in the section below.

The current finite-audit support remains the recorded result documentation:

- `docs/m4_semantic_encoding_boundary.md`
- `docs/m4_scope_decision_mask_shape_phase_diagram.md`
- `docs/m4_mask_shape_collapse_law_audit_result.md`
- `docs/m4_certificate2_phase_diagram_checker_result.md`
- `docs/m4_finite_data_closure_note.md`

These documents support the manuscript's finite-data claim under the declared
M4/Sen24 encoding. The replay wrapper below supplies the missing one-command
rerun recipe.

## M4 finite-audit checker replay

Case classification: Case B.

Replay wrapper:

```text
papers/m4/repro/run_m4_finite_audit_replay.sh
```

The wrapper only invokes existing scripts with fixed arguments and writes
generated replay outputs under:

```text
/tmp/sen_m4_repro
```

Replay command:

```text
papers/m4/repro/run_m4_finite_audit_replay.sh
```

Exit status: `0`.

Tracked logs and summaries:

- `papers/m4/repro/m4_finite_audit_environment.log`
- `papers/m4/repro/m4_finite_audit_checker.log`
- `papers/m4/repro/m4_finite_audit_replay_summary.md`

The replay reproduced the documented headline values: 48 total cells, 18
`ALL_UNSAT` cells, 30 `ALL_SAT` cells, 0 `MIXED_WITHIN_SHAPE` cells, 0
`UNKNOWN` cells, 816 repair objects, 46 repair orbits, 46 cell report fibers,
33 shape-blind fibers, `PASS` support truncation, `PASS` orbit/fiber
exactness, `PASS` active `RepairEmpty`, and `PASS` Certificate 2 verdict.

The finite-audit checker-command release blocker is resolved by this replay
wrapper and the tracked logs. This does not prove checker correctness,
semantic-to-CNF correctness, Python encoder correctness, or Lean verification
of the whole finite certificate.

## 5. File hashes

SHA-256 hashes are recorded in:

```text
papers/m4/repro/m4_v0_1_hashes.sha256
```

The manifest covers:

- `SocialChoiceAtlas/Sen/RightAtomBridge.lean`
- `docs/m4_semantic_encoding_boundary.md`
- `docs/m4_scope_decision_mask_shape_phase_diagram.md`
- `docs/m4_mask_shape_collapse_law_audit_result.md`
- `docs/m4_certificate2_phase_diagram_checker_result.md`
- `docs/m4_finite_data_closure_note.md`
- `papers/m4/repro/right_atom_bridge_lean_check.log`
- `papers/m4/repro/run_m4_finite_audit_replay.sh`
- `papers/m4/repro/m4_finite_audit_environment.log`
- `papers/m4/repro/m4_finite_audit_checker.log`
- `papers/m4/repro/m4_finite_audit_replay_summary.md`

No PDF, auxiliary LaTeX file, solver output, generated CNF/LRAT artifact, or
temporary finite-audit output is included in this hash manifest.

## 6. Build command

The full LaTeX/BibTeX validation sequence for this workspace is:

```text
cd papers/m4
lualatex -interaction=nonstopmode -halt-on-error -output-directory=/tmp/sen_m4_latex_build main.tex
cd /tmp/sen_m4_latex_build
BIBINPUTS=/path/to/Sen-Lean4/papers/m4: bibtex main
cd /path/to/Sen-Lean4/papers/m4
lualatex -interaction=nonstopmode -halt-on-error -output-directory=/tmp/sen_m4_latex_build main.tex
lualatex -interaction=nonstopmode -halt-on-error -output-directory=/tmp/sen_m4_latex_build main.tex
```

The `/path/to/Sen-Lean4` placeholder should be replaced with the local
repository path. Build outputs are temporary artifacts and should not be
committed unless a later release policy explicitly requests them.

## 7. What this note does not prove

This note does not prove:

- Python encoder correctness;
- `_right_clauses` correctness;
- `FiniteSchema` profile correctness;
- SAT assignment semantics as Lean social welfare functions;
- semantic-to-CNF correctness;
- CNF artifact correctness;
- full selector-free equivalence to Lean `MINLIB`;
- correctness of the finite-audit checker as a Lean theorem;
- structural necessity of the Mask-Shape Collapse Law;
- a new general Sen theorem;
- family-scale CNF/LRAT/atlas/repair lifts.

The Lean log exposes a reproducibility check for the Level B semantic bridge.
The finite-audit result documents expose recorded finite-data evidence under
the declared encoding. Neither closes Level C artifact correctness.

## 8. Remaining future assurance obligations

Future assurance work should include:

- a Lean reconstruction or independent formalization of the finite-audit
  checker obligations;
- a representation map between Lean profiles and finite schema profiles;
- a mapping between Lean strict preference predicates and generator variables;
- SAT assignment semantics;
- a proof that Python right clauses encode the Lean right-condition semantics;
- artifact-level correctness for generated CNF.

These are future Level C / checker-hardening obligations. They are not current
M4 claims.
