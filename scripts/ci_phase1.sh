#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
TMP_DIR="$(mktemp -d)"
trap 'rm -rf "$TMP_DIR"' EXIT

python3 "$ROOT_DIR/scripts/gen_dimacs.py" \
  --n 2 --m 4 \
  --axioms asymm,un,minlib,no_cycle3,no_cycle4 \
  --out "$TMP_DIR/sen24.cnf" \
  --manifest "$TMP_DIR/sen24.manifest.json"

python3 "$ROOT_DIR/scripts/check_sen24_cnf.py" \
  "$TMP_DIR/sen24.cnf" \
  --manifest "$TMP_DIR/sen24.manifest.json"

python3 "$ROOT_DIR/scripts/check_sen24_cnf.py" \
  "$ROOT_DIR/Certificates/sen24.cnf" \
  --manifest "$ROOT_DIR/Certificates/sen24.manifest.json"

cd "$ROOT_DIR"
lake build SocialChoiceAtlas.Sen.BaseCase24.SATSenCNF

