#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)"
ROOT="$(CDPATH= cd -- "$SCRIPT_DIR/.." && pwd)"
cd "$ROOT"

MODULE_FILES=(
  "SocialChoiceAtlas/Reportability/Defs.lean"
  "SocialChoiceAtlas/Reportability/Atomic.lean"
  "SocialChoiceAtlas/Reportability/GroupSound.lean"
  "SocialChoiceAtlas/Reportability/Monotone.lean"
  "SocialChoiceAtlas/Reportability/Examples.lean"
)

for module_file in "${MODULE_FILES[@]}"; do
  lake env lean "$module_file"
done

if grep -RInE '\bsorry\b|\badmit\b|aesop\?|exact\?' SocialChoiceAtlas/Reportability; then
  echo "Forbidden proof marker found in SocialChoiceAtlas/Reportability" >&2
  exit 1
fi

TMP_DIR="$(mktemp -d "${TMPDIR:-/tmp}/m3-smoke.XXXXXX")"
trap 'rm -rf "$TMP_DIR"' EXIT

AUDIT_FILE="$TMP_DIR/M3AxiomAudit.lean"
AUDIT_OUT="$TMP_DIR/axioms.out"

cat > "$AUDIT_FILE" <<'LEAN'
import SocialChoiceAtlas.Reportability.Examples

#print axioms SocialChoiceAtlas.Reportability.m3a_grouped_correctness
#print axioms SocialChoiceAtlas.Reportability.m3a_raw_transport
#print axioms SocialChoiceAtlas.Reportability.m3b_grouped_correctness
#print axioms SocialChoiceAtlas.Reportability.m3b_two_realization
#print axioms SocialChoiceAtlas.Reportability.audit_cost_collapse
#print axioms SocialChoiceAtlas.Reportability.m3c_converse
#print axioms SocialChoiceAtlas.Reportability.groupSoundness_iff
#print axioms SocialChoiceAtlas.Reportability.atomicity_implies_groupSoundness
LEAN

lake env lean "$AUDIT_FILE" > "$AUDIT_OUT"
cat "$AUDIT_OUT"

python3 - "$AUDIT_OUT" <<'PY'
import re
import sys

path = sys.argv[1]
text = open(path, encoding="utf-8").read()
decls = [
    "SocialChoiceAtlas.Reportability.m3a_grouped_correctness",
    "SocialChoiceAtlas.Reportability.m3a_raw_transport",
    "SocialChoiceAtlas.Reportability.m3b_grouped_correctness",
    "SocialChoiceAtlas.Reportability.m3b_two_realization",
    "SocialChoiceAtlas.Reportability.audit_cost_collapse",
    "SocialChoiceAtlas.Reportability.m3c_converse",
    "SocialChoiceAtlas.Reportability.groupSoundness_iff",
    "SocialChoiceAtlas.Reportability.atomicity_implies_groupSoundness",
]
allowed = {"propext", "Classical.choice", "Quot.sound"}

for decl in decls:
    pattern = re.compile(
        r"'" + re.escape(decl) + r"' depends on axioms:\s*\[(.*?)\]",
        re.DOTALL,
    )
    match = pattern.search(text)
    if not match:
        print(f"missing axiom output for {decl}", file=sys.stderr)
        sys.exit(1)
    found = {item.strip() for item in match.group(1).replace("\n", " ").split(",")}
    found.discard("")
    if found != allowed:
        print(
            f"unexpected axioms for {decl}: {sorted(found)}; "
            f"expected {sorted(allowed)}",
            file=sys.stderr,
        )
        sys.exit(1)

print("M3 axiom audit passed")
PY

