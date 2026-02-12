#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
TMP_DIR="$(mktemp -d)"
trap 'rm -rf "$TMP_DIR"' EXIT

OUT_DIR="$TMP_DIR/atlas_v1"

python3 "$ROOT_DIR/scripts/run_atlas.py" \
  --dry-run \
  --jobs 2 \
  --prune none \
  --case-masks 0,1,31 \
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

