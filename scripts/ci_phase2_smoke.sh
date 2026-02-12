#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
TMP_DIR="$(mktemp -d)"
trap 'rm -rf "$TMP_DIR"' EXIT

OUT_DIR="$TMP_DIR/atlas_v1"

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
