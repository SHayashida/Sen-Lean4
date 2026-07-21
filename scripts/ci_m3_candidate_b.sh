#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)"
ROOT="$(CDPATH= cd -- "$SCRIPT_DIR/.." && pwd)"
cd "$ROOT"

python3 m3/candidate_b/build_package.py --source-mode curated

python3 tools/m3_candidate_b/validate_candidate_b.py \
  --contract m3/candidate_b/contract.json \
  --case-schema m3/candidate_b/case_schema.json \
  --source-artifacts m3/candidate_b/source_artifacts.json \
  --evidence m3/candidate_b/evidence \
  --theorem-binding m3/candidate_b/theorem_binding.json \
  --out m3/candidate_b/generated \
  --repo-root .

python3 -m unittest discover -s tools/m3_candidate_b/tests -v
python3 m3/candidate_b/verify_manifest.py
./scripts/ci_m3_smoke.sh

git diff --exit-code -- m3/candidate_b
