#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
TMP_DIR="$(mktemp -d)"
trap 'rm -rf "$TMP_DIR"' EXIT

BASE_CNF_TMP="$TMP_DIR/sen24.cnf"
BASE_MAN_TMP="$TMP_DIR/sen24.manifest.json"

python3 "$ROOT_DIR/scripts/gen_dimacs.py" \
  --n 2 --m 4 \
  --axioms asymm,un,minlib,no_cycle3,no_cycle4 \
  --out "$BASE_CNF_TMP" \
  --manifest "$BASE_MAN_TMP"

python3 "$ROOT_DIR/scripts/check_sen24_cnf.py" \
  "$BASE_CNF_TMP" \
  --manifest "$BASE_MAN_TMP" \
  --strict-duplicates \
  --fail-on-tautology

python3 "$ROOT_DIR/scripts/check_sen24_cnf.py" \
  "$ROOT_DIR/Certificates/sen24.cnf" \
  --manifest "$ROOT_DIR/Certificates/sen24.manifest.json" \
  --strict-duplicates \
  --fail-on-tautology

cmp -s "$BASE_CNF_TMP" "$ROOT_DIR/Certificates/sen24.cnf"
cmp -s "$BASE_MAN_TMP" "$ROOT_DIR/Certificates/sen24.manifest.json"

python3 "$ROOT_DIR/scripts/gen_sen24_dimacs.py" \
  --out "$TMP_DIR/sen24.wrapper.cnf" \
  --manifest-out "$TMP_DIR/sen24.wrapper.manifest.json"
cmp -s "$BASE_CNF_TMP" "$TMP_DIR/sen24.wrapper.cnf"
cmp -s "$BASE_MAN_TMP" "$TMP_DIR/sen24.wrapper.manifest.json"

python3 "$ROOT_DIR/scripts/gen_dimacs.py" \
  --n 2 --m 4 \
  --axioms asymm,un,no_cycle3,no_cycle4 \
  --out "$TMP_DIR/sen24.no_minlib.cnf" \
  --manifest "$TMP_DIR/sen24.no_minlib.manifest.json"

python3 "$ROOT_DIR/scripts/check_sen24_cnf.py" \
  "$TMP_DIR/sen24.no_minlib.cnf" \
  --manifest "$TMP_DIR/sen24.no_minlib.manifest.json" \
  --strict-duplicates \
  --fail-on-tautology

cd "$ROOT_DIR"
lake build SocialChoiceAtlas.Sen.BaseCase24.SATSenCNF
