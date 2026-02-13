#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
TMP_DIR="$(mktemp -d)"
trap 'rm -rf "$TMP_DIR"' EXIT

OUT_DIR="$TMP_DIR/atlas_v1"
SYM_OUT="$TMP_DIR/atlas_sym"
PRUNE_OUT="$TMP_DIR/atlas_prune"

test -f "$ROOT_DIR/docs/related_work_notes.md"
test -f "$ROOT_DIR/docs/paper_claims_map.md"
test -f "$ROOT_DIR/docs/reproducibility_appendix.md"

grep -q "scripts/run_atlas.py" "$ROOT_DIR/docs/paper_claims_map.md"
grep -q "scripts/mus_mcs.py" "$ROOT_DIR/docs/paper_claims_map.md"
grep -q "Case11111" "$ROOT_DIR/docs/paper_claims_map.md"

grep -q "atlas_schema_version" "$ROOT_DIR/docs/reproducibility_appendix.md"
grep -q "solver_version_raw" "$ROOT_DIR/docs/reproducibility_appendix.md"
grep -q "Certificates/atlas/case_11111" "$ROOT_DIR/docs/reproducibility_appendix.md"

grep -q "ATMS" "$ROOT_DIR/docs/related_work_notes.md"
grep -q "MAXSAT" "$ROOT_DIR/docs/related_work_notes.md"
grep -q "OMT" "$ROOT_DIR/docs/related_work_notes.md"
grep -q "Constraint Hierarchies" "$ROOT_DIR/docs/related_work_notes.md"

python3 "$ROOT_DIR/scripts/run_atlas.py" \
  --jobs 1 \
  --prune none \
  --case-masks 0,1,31 \
  --emit-proof unsat-only \
  --outdir "$OUT_DIR"

test -f "$OUT_DIR/atlas.json"

for case_id in case_00000 case_10000 case_11111; do
  test -f "$OUT_DIR/$case_id/sen24.cnf"
  test -f "$OUT_DIR/$case_id/sen24.manifest.json"
  test -f "$OUT_DIR/$case_id/solver.log"
  test -f "$OUT_DIR/$case_id/summary.json"
done

python3 - "$OUT_DIR/atlas.json" "$OUT_DIR/case_11111/summary.json" <<'PY'
import json
import sys
from pathlib import Path

atlas = json.loads(Path(sys.argv[1]).read_text())
schema_version = atlas.get("atlas_schema_version")
if not isinstance(schema_version, int) or schema_version < 1:
    raise SystemExit("atlas_schema_version missing or invalid")
summary = json.loads(Path(sys.argv[2]).read_text())
for obj_name, obj in [("atlas", atlas), ("summary", summary)]:
    solver_info = obj.get("solver_info")
    env_info = obj.get("environment_info")
    if not isinstance(solver_info, dict):
        raise SystemExit(f"{obj_name}: missing solver_info")
    for k in ("solver_path", "solver_version_raw", "solver_version", "solver_sha256"):
        if k not in solver_info:
            raise SystemExit(f"{obj_name}: missing solver_info.{k}")
    if not isinstance(env_info, dict):
        raise SystemExit(f"{obj_name}: missing environment_info")
    for k in ("python_version", "platform", "git_commit"):
        if k not in env_info:
            raise SystemExit(f"{obj_name}: missing environment_info.{k}")
print("runtime_meta_ok")
PY

python3 "$ROOT_DIR/scripts/check_sen24_cnf.py" \
  "$OUT_DIR/case_00000/sen24.cnf" \
  --manifest "$OUT_DIR/case_00000/sen24.manifest.json" \
  --strict-duplicates \
  --fail-on-tautology

python3 "$ROOT_DIR/scripts/check_sen24_cnf.py" \
  "$OUT_DIR/case_10000/sen24.cnf" \
  --manifest "$OUT_DIR/case_10000/sen24.manifest.json" \
  --strict-duplicates \
  --fail-on-tautology

python3 "$ROOT_DIR/scripts/check_sen24_cnf.py" \
  "$OUT_DIR/case_11111/sen24.cnf" \
  --manifest "$OUT_DIR/case_11111/sen24.manifest.json" \
  --strict-duplicates \
  --fail-on-tautology

test -s "$OUT_DIR/case_11111/proof.lrat"

python3 - "$OUT_DIR/case_11111/summary.json" <<'PY'
import json
import sys
from pathlib import Path
summary = json.loads(Path(sys.argv[1]).read_text())
proof = summary.get("proof")
if summary.get("status") != "UNSAT":
    raise SystemExit("case_11111 is not UNSAT in smoke run")
if not proof or proof.get("format") != "lrat" or proof.get("path") != "proof.lrat":
    raise SystemExit("missing proof metadata in case_11111 summary")
if not proof.get("sha256"):
    raise SystemExit("missing proof sha256 in case_11111 summary")
manifest = summary.get("manifest", {})
if not manifest.get("cnf_sha256"):
    raise SystemExit("missing cnf sha256 in case_11111 summary")
if not summary.get("reproduce", {}).get("command"):
    raise SystemExit("missing reproduce command in case_11111 summary")
print("proof_meta_ok")
PY

cd "$ROOT_DIR"
lake build SocialChoiceAtlas.Sen.Atlas.Case11111

python3 "$ROOT_DIR/scripts/mus_mcs.py" \
  --outdir "$OUT_DIR" \
  --case-ids case_11111 \
  --max-unsat-cases 1 \
  --max-pair-trials 10

test -f "$OUT_DIR/case_11111/mus.json"
test -f "$OUT_DIR/case_11111/mcs.json"

python3 - "$OUT_DIR/atlas.json" <<'PY'
import json
import sys
from pathlib import Path

atlas = json.loads(Path(sys.argv[1]).read_text())
case = next(c for c in atlas["cases"] if c["case_id"] == "case_11111")
mus = case.get("mus")
if mus is None or mus.get("status") != "ok":
    raise SystemExit("missing mus for case_11111")
mus_axioms = list(mus.get("mus_axioms", []))
if len(mus_axioms) == 0:
    raise SystemExit("mus is empty for case_11111")
on_axioms = set(case.get("axioms_on", []))
if not set(mus_axioms).issubset(on_axioms):
    raise SystemExit("mus axioms are not a subset of case on_axioms")
mcs = case.get("mcs", {})
removed = set(mcs.get("removed_axioms", []))
if not removed.issubset(on_axioms):
    raise SystemExit("mcs removed axioms are not a subset of case on_axioms")
print("mus_ok", mus.get("mus_bits"), "mus_size", len(mus_axioms))
PY

python3 "$ROOT_DIR/scripts/decode_model.py" --case-dir "$OUT_DIR/case_00000"
test -s "$OUT_DIR/case_00000/rule.md"

python3 "$ROOT_DIR/scripts/summarize_atlas.py" --outdir "$OUT_DIR"
test -s "$OUT_DIR/atlas_summary.md"
grep -q "UNSAT cases" "$OUT_DIR/atlas_summary.md"
grep -q "case_11111" "$OUT_DIR/atlas_summary.md"

python3 "$ROOT_DIR/scripts/run_atlas.py" \
  --jobs 1 \
  --prune none \
  --symmetry alts \
  --symmetry-check \
  --case-masks 0,1,31 \
  --emit-proof never \
  --outdir "$SYM_OUT"

python3 - "$SYM_OUT/atlas.json" <<'PY'
import json
import sys
from pathlib import Path

atlas = json.loads(Path(sys.argv[1]).read_text())
if atlas.get("symmetry_mode") != "alts":
    raise SystemExit("symmetry_mode is not alts")
if int(atlas.get("equiv_classes_total", 0)) < 1:
    raise SystemExit("equiv_classes_total missing/invalid")
symmetry_check = atlas.get("symmetry_check", {})
if not isinstance(symmetry_check, dict):
    raise SystemExit("missing symmetry_check block")
if symmetry_check.get("enabled") is not True:
    raise SystemExit("symmetry_check should be enabled")
if "checked_k" not in symmetry_check or "mismatches" not in symmetry_check:
    raise SystemExit("symmetry_check stats are incomplete")
if "checked_cases" not in symmetry_check:
    raise SystemExit("symmetry_check.checked_cases is missing")
if int(symmetry_check.get("mismatches", -1)) != 0:
    raise SystemExit("symmetry_check mismatches should be 0 in smoke run")
checked_cases = atlas.get("checked_cases")
if not isinstance(checked_cases, list):
    raise SystemExit("atlas.checked_cases is missing")
cases = atlas.get("cases", [])
if not isinstance(cases, list) or not cases:
    raise SystemExit("missing cases in symmetry run")
sample = cases[0]
if not sample.get("equiv_class_id") or not sample.get("representative_case"):
    raise SystemExit("missing per-case symmetry mapping")
print("symmetry_ok", atlas.get("equiv_classes_total"))
PY

python3 "$ROOT_DIR/scripts/run_atlas.py" \
  --jobs 1 \
  --prune monotone \
  --prune-check \
  --emit-proof never \
  --outdir "$PRUNE_OUT"

python3 - "$PRUNE_OUT/atlas.json" <<'PY'
import json
import sys
from pathlib import Path

atlas = json.loads(Path(sys.argv[1]).read_text())
if int(atlas.get("cases_total", -1)) != 32:
    raise SystemExit("cases_total mismatch for prune run")
status = atlas.get("status_counts", {})
sat = int(status.get("SAT", 0))
unsat = int(status.get("UNSAT", 0))
unknown = int(status.get("UNKNOWN", 0))
if sat + unsat + unknown != 32:
    raise SystemExit("status totals do not match cases_total")
if sat != 30 or unsat != 2:
    raise SystemExit(f"unexpected SAT/UNSAT totals: SAT={sat} UNSAT={unsat}")
cases = atlas.get("cases", [])
pruned = [c for c in cases if not bool(c.get("solved", False))]
if not pruned:
    raise SystemExit("expected at least one inferred/pruned case")
for c in pruned:
    if c.get("status") in {"SAT", "UNSAT"} and not c.get("pruned_by"):
        raise SystemExit("inferred SAT/UNSAT case missing pruned_by metadata")
    if c.get("status") in {"SAT", "UNSAT"}:
        pb = c["pruned_by"]
        for key in ("derived_status", "rule", "witness_case_id"):
            if key not in pb:
                raise SystemExit(f"missing pruned_by.{key} in inferred case {c.get('case_id')}")
prune_stats = atlas.get("prune_stats", {})
if int(prune_stats.get("solver_calls_avoided", 0)) <= 0:
    raise SystemExit("solver_calls_avoided should be positive in monotone prune run")
print("prune_ok", len(pruned))
PY

python3 "$ROOT_DIR/scripts/summarize_atlas.py" --outdir "$PRUNE_OUT"
test -s "$PRUNE_OUT/atlas_summary.md"
grep -q "Symmetry classes" "$PRUNE_OUT/atlas_summary.md"
