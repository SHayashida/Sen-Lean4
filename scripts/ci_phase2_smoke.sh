#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
TMP_DIR="$(mktemp -d)"
trap 'rm -rf "$TMP_DIR"' EXIT

OUT_DIR="$TMP_DIR/atlas_v1"
SYM_OUT="$TMP_DIR/atlas_sym"
PRUNE_OUT="$TMP_DIR/atlas_prune"
REPAIRS_OUT="$TMP_DIR/atlas_repairs"
HASSE_OUT="$TMP_DIR/hasse_frontier"
TRI_OUT="$TMP_DIR/triangulation"
EVAL_OUT="$TMP_DIR/eval_smoke"

test -f "$ROOT_DIR/docs/related_work_notes.md"
test -f "$ROOT_DIR/docs/paper_claims_map.md"
test -f "$ROOT_DIR/docs/reproducibility_appendix.md"
test -f "$ROOT_DIR/docs/public_repo_security.md"
test -f "$ROOT_DIR/docs/evaluation_plan.md"
test -f "$ROOT_DIR/docs/sat_gallery.md"
test -f "$ROOT_DIR/paper/main.tex"
test -f "$ROOT_DIR/paper/README.md"
test -f "$ROOT_DIR/paper/sections/00_abstract.tex"
test -f "$ROOT_DIR/paper/sections/01_intro.tex"
test -f "$ROOT_DIR/paper/sections/02_problem_and_positioning.tex"
test -f "$ROOT_DIR/paper/sections/03_system_design.tex"
test -f "$ROOT_DIR/paper/sections/04_methods.tex"
test -f "$ROOT_DIR/paper/sections/05_evaluation.tex"
test -f "$ROOT_DIR/paper/sections/06_case_study_sen24.tex"
test -f "$ROOT_DIR/paper/sections/07_related_work.tex"
test -f "$ROOT_DIR/paper/sections/08_limitations_and_scope.tex"
test -f "$ROOT_DIR/paper/sections/09_conclusion.tex"
test -f "$ROOT_DIR/paper/sections/appendix_repro.tex"

# doc gate strategy: stable heading/label anchors (avoid brittle prose-phrase matching)
grep -q '^## C1\.' "$ROOT_DIR/docs/paper_claims_map.md"
grep -q '^## C2\.' "$ROOT_DIR/docs/paper_claims_map.md"
grep -q '^## C3\.' "$ROOT_DIR/docs/paper_claims_map.md"
grep -q '^## C4\.' "$ROOT_DIR/docs/paper_claims_map.md"
grep -q '^## C5\.' "$ROOT_DIR/docs/paper_claims_map.md"
grep -q '^## C6\.' "$ROOT_DIR/docs/paper_claims_map.md"

grep -Fq '## Artifact policy' "$ROOT_DIR/docs/reproducibility_appendix.md"
grep -Fq '## `atlas_schema_version` policy' "$ROOT_DIR/docs/reproducibility_appendix.md"
grep -Fq '## Solver metadata policy' "$ROOT_DIR/docs/reproducibility_appendix.md"

grep -Fq '## Positioning (short)' "$ROOT_DIR/docs/related_work_notes.md"
grep -Fq '## Comparison matrix' "$ROOT_DIR/docs/related_work_notes.md"
grep -Fq '## What we do not claim' "$ROOT_DIR/docs/related_work_notes.md"

grep -Fq '## AGENTS policy' "$ROOT_DIR/docs/public_repo_security.md"
grep -Fq '## CI secret handling' "$ROOT_DIR/docs/public_repo_security.md"
grep -Fq '## Least-privilege `GITHUB_TOKEN`' "$ROOT_DIR/docs/public_repo_security.md"

grep -Fq '## Metrics' "$ROOT_DIR/docs/evaluation_plan.md"
grep -Fq '## Configurations' "$ROOT_DIR/docs/evaluation_plan.md"
grep -Fq '## Reproducibility' "$ROOT_DIR/docs/evaluation_plan.md"

grep -Fq '## Motivation' "$ROOT_DIR/docs/sat_gallery.md"
grep -Fq '## Non-trivial heuristics' "$ROOT_DIR/docs/sat_gallery.md"
grep -Fq '## Reproduction commands' "$ROOT_DIR/docs/sat_gallery.md"

grep -Fq '## Build' "$ROOT_DIR/paper/README.md"
grep -Fq '## Reproduce figures' "$ROOT_DIR/paper/README.md"
grep -Fq '## Public repo safety' "$ROOT_DIR/paper/README.md"

python3 "$ROOT_DIR/scripts/plot_frontier.py" --help >/dev/null
python3 "$ROOT_DIR/scripts/plot_hasse_frontier.py" --help >/dev/null
python3 "$ROOT_DIR/scripts/enumerate_repairs.py" --help >/dev/null
python3 "$ROOT_DIR/scripts/triangulate_repairs.py" --help >/dev/null
python3 "$ROOT_DIR/scripts/enumerate_repairs.py" --help >/dev/null

# AGENTS public-safety gates
if grep -nE '[ぁ-んァ-ヶ一-龯]' "$ROOT_DIR/AGENTS.md"; then
  echo "AGENTS.md must be English-only (Japanese script detected)." >&2
  exit 1
fi
if grep -nEi 'API_KEY=|BEGIN[[:space:]]+PRIVATE[[:space:]]+KEY|token=' "$ROOT_DIR/AGENTS.md"; then
  echo "AGENTS.md contains secret-like patterns." >&2
  exit 1
fi

python3 "$ROOT_DIR/scripts/run_atlas.py" \
  --jobs 1 \
  --prune none \
  --case-masks 0,2,31 \
  --emit-proof unsat-only \
  --outdir "$OUT_DIR"

test -f "$OUT_DIR/atlas.json"

for case_id in case_00000 case_01000 case_11111; do
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
  "$OUT_DIR/case_01000/sen24.cnf" \
  --manifest "$OUT_DIR/case_01000/sen24.manifest.json" \
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

python3 "$ROOT_DIR/scripts/run_atlas.py" \
  --jobs 1 \
  --prune none \
  --emit-proof never \
  --outdir "$REPAIRS_OUT"

python3 "$ROOT_DIR/scripts/enumerate_repairs.py" \
  --outdir "$REPAIRS_OUT"

python3 - "$REPAIRS_OUT/atlas.json" <<'PY'
import itertools
import json
import re
import sys
from pathlib import Path

atlas_path = Path(sys.argv[1])
atlas = json.loads(atlas_path.read_text())
cases = atlas.get("cases", [])
if int(atlas.get("cases_total", -1)) != 32:
    raise SystemExit("repairs atlas must include 32 solved cases")
case_by_mask = {int(c["mask_int"]): c for c in cases}
width = len(atlas.get("axiom_universe", []))
if width != 5:
    raise SystemExit("expected 5 axioms for sen24 repair smoke check")

unsat_cases = [c for c in cases if c.get("status") == "UNSAT" and bool(c.get("solved", False))]
if not unsat_cases:
    raise SystemExit("expected solved UNSAT cases for repair enumeration")

for c in unsat_cases:
    repairs = c.get("mcs_all")
    if not isinstance(repairs, list) or not repairs:
        raise SystemExit(f"UNSAT case missing non-empty mcs_all: {c.get('case_id')}")

sample = unsat_cases[0]
repairs = sample["mcs_all"]
for repair in repairs:
    remove_mask = int(repair["remove_mask_int"])
    sat_mask = int(sample["mask_int"]) & ~remove_mask
    sat_case = case_by_mask.get(sat_mask)
    if sat_case is None or sat_case.get("status") != "SAT":
        raise SystemExit("mcs_all contains non-SAT repair target")
    idxs = [i for i in range(width) if (remove_mask >> i) & 1]
    for r in range(len(idxs)):
        for sub in itertools.combinations(idxs, r):
            sub_mask = 0
            for i in sub:
                sub_mask |= 1 << i
            sub_case = case_by_mask[int(sample["mask_int"]) & ~sub_mask]
            if sub_case.get("status") != "UNSAT":
                raise SystemExit("mcs_all minimality check failed in smoke validation")

atlas_text = atlas_path.read_text()
if "/Users/" in atlas_text:
    raise SystemExit("repair atlas output leaks '/Users/' absolute path")
if re.search(r"[A-Za-z]:\\\\", atlas_text):
    raise SystemExit("repair atlas output leaks Windows absolute path")

print("repairs_ok", len(unsat_cases), "sample_case", sample.get("case_id"))
PY

python3 "$ROOT_DIR/scripts/plot_hasse_frontier.py" \
  --atlas-outdir "$REPAIRS_OUT" \
  --outdir "$HASSE_OUT" \
  --format png \
  --include-pruned false \
  --show status

test -s "$HASSE_OUT/frontier_hasse.dot"
test -s "$HASSE_OUT/frontier_hasse.png"

python3 - "$HASSE_OUT/frontier_hasse.dot" <<'PY'
import re
import sys
from pathlib import Path

dot_text = Path(sys.argv[1]).read_text()
nodes = set(re.findall(r'"(case_[01]{5})"\s+\[', dot_text))
if len(nodes) != 32:
    raise SystemExit(f"hasse dot must contain 32 case nodes, got {len(nodes)}")
if "/Users/" in dot_text:
    raise SystemExit("hasse dot leaks '/Users/' absolute path")
if re.search(r"[A-Za-z]:\\\\", dot_text):
    raise SystemExit("hasse dot leaks Windows absolute path")
print("hasse_ok", len(nodes))
PY

python3 "$ROOT_DIR/scripts/triangulate_repairs.py" \
  --atlas-outdir "$REPAIRS_OUT" \
  --outdir "$TRI_OUT" \
  --backend bruteforce

test -s "$TRI_OUT/repair_triangulation.json"
test -s "$TRI_OUT/repair_triangulation.md"

python3 - "$TRI_OUT/repair_triangulation.json" "$TRI_OUT/repair_triangulation.md" <<'PY'
import json
import re
import sys
from pathlib import Path

obj = json.loads(Path(sys.argv[1]).read_text())
cases = obj.get("cases", [])
if not isinstance(cases, list) or not cases:
    raise SystemExit("triangulation report has no case entries")
for case in cases:
    compare = case.get("compare", {})
    if compare.get("size_match") is not True:
        raise SystemExit(f"triangulation size mismatch: {case.get('case_id')}")
    if compare.get("set_match") is not True:
        raise SystemExit(f"triangulation set mismatch: {case.get('case_id')}")

json_text = Path(sys.argv[1]).read_text()
md_text = Path(sys.argv[2]).read_text()
if "/Users/" in json_text or "/Users/" in md_text:
    raise SystemExit("triangulation output leaks '/Users/' absolute path")
if re.search(r"[A-Za-z]:\\\\", json_text) or re.search(r"[A-Za-z]:\\\\", md_text):
    raise SystemExit("triangulation output leaks Windows absolute path")
print("triangulation_ok", len(cases))
PY

python3 "$ROOT_DIR/scripts/eval_atlas.py" \
  --outdir "$EVAL_OUT" \
  --repeat 1 \
  --configs none_none \
  --jobs 1 \
  --case-masks 0,1,31

MPLBACKEND=Agg python3 "$ROOT_DIR/scripts/plot_eval.py" \
  --eval-json "$EVAL_OUT/eval.json"

test -s "$EVAL_OUT/eval.json"
test -s "$EVAL_OUT/eval.csv"
test -s "$EVAL_OUT/figures/runtime_boxplot.png"

python3 - "$EVAL_OUT/eval.json" <<'PY'
import json
import sys
from pathlib import Path

obj = json.loads(Path(sys.argv[1]).read_text())
schema = obj.get("eval_schema_version")
if not isinstance(schema, int) or schema < 1:
    raise SystemExit("eval_schema_version missing or invalid")

repro = obj.get("reproducibility")
if not isinstance(repro, dict):
    raise SystemExit("missing reproducibility block")

git = repro.get("git", {})
py = repro.get("python", {})
solver = repro.get("solver", {})
if not isinstance(git, dict) or "commit" not in git:
    raise SystemExit("missing reproducibility.git.commit")
if not isinstance(py, dict) or "version" not in py:
    raise SystemExit("missing reproducibility.python.version")
if "platform" not in repro:
    raise SystemExit("missing reproducibility.platform")
if not isinstance(solver, dict):
    raise SystemExit("missing reproducibility.solver")
for k in ("version_raw", "version", "path", "sha256"):
    if k not in solver:
        raise SystemExit(f"missing reproducibility.solver.{k}")
if "/Users/" in str(solver.get("path", "")):
    raise SystemExit("reproducibility.solver.path must be sanitized")

seeds = obj.get("seeds")
if not isinstance(seeds, list) or not seeds:
    raise SystemExit("missing seeds[]")
if "seed_policy" not in obj:
    raise SystemExit("missing seed_policy")
print("eval_meta_ok")
PY

python3 "$ROOT_DIR/scripts/build_sat_gallery.py" \
  --atlas-outdir "$REPAIRS_OUT" \
  --top-k 2 \
  --min-k 1

test -s "$REPAIRS_OUT/gallery.json"
test -s "$REPAIRS_OUT/gallery.md"

python3 - "$REPAIRS_OUT/gallery.json" "$REPAIRS_OUT/gallery.md" <<'PY'
import json
import re
import sys
from pathlib import Path

gallery = json.loads(Path(sys.argv[1]).read_text())
gallery_md = Path(sys.argv[2]).read_text()

schema = gallery.get("gallery_schema_version")
if not isinstance(schema, int) or schema < 1:
    raise SystemExit("gallery_schema_version missing or invalid")

entries = gallery.get("entries", [])
if not isinstance(entries, list) or len(entries) < 1:
    raise SystemExit("gallery must contain at least one entry")

for entry in entries:
    if entry.get("model_validated") is not True:
        raise SystemExit(f"gallery entry not validated: {entry.get('case_id')}")
    if entry.get("non_trivial") is not True:
        raise SystemExit(f"gallery entry failed non-trivial filter: {entry.get('case_id')}")
    report = entry.get("nontriviality_report", {})
    if report.get("passes_non_triviality") is not True:
        raise SystemExit(f"gallery entry missing nontriviality report pass: {entry.get('case_id')}")
    files = entry.get("files", {})
    for _, path in files.items():
        if path is None:
            continue
        if str(path).startswith("/"):
            raise SystemExit("gallery file path must be relative")
        if re.match(r"^[A-Za-z]:\\\\", str(path)):
            raise SystemExit("gallery file path must not use Windows absolute prefix")

rule_card = entries[0].get("files", {}).get("rule_card_md")
if not rule_card:
    raise SystemExit("rule_card_md missing from first gallery entry")
rule_card_path = Path(sys.argv[1]).parent / rule_card
if not rule_card_path.exists() or rule_card_path.stat().st_size == 0:
    raise SystemExit("rule_card.md missing or empty")
rule_card_text = rule_card_path.read_text()
for anchor in ("# Rule Card:", "## Key metrics", "## Profile witnesses"):
    if anchor not in rule_card_text:
        raise SystemExit(f"rule_card.md missing anchor: {anchor}")

gallery_text = json.dumps(gallery, sort_keys=True)
if "/Users/" in gallery_text or "/Users/" in gallery_md or "/Users/" in rule_card_text:
    raise SystemExit("gallery output leaks '/Users/' absolute path")
if re.search(r"[A-Za-z]:\\\\", gallery_text) or re.search(r"[A-Za-z]:\\\\", gallery_md) or re.search(r"[A-Za-z]:\\\\", rule_card_text):
    raise SystemExit("gallery output leaks Windows absolute path")

print("gallery_ok", len(entries))
PY
