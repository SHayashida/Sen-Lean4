#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
SEN_DIR="$ROOT_DIR/SocialChoiceAtlas/Sen"
LIFTING_DIR="$ROOT_DIR/SocialChoiceAtlas/Sen/Lifting"
LIFTING_MODULE="$LIFTING_DIR/ImpossibilityLift.lean"
OBSTRUCTION_BASIS="$SEN_DIR/ObstructionBasis.lean"
OBSTRUCTION_PROFILES="$SEN_DIR/ObstructionProfiles.lean"
OBSTRUCTION_SOUNDNESS="$SEN_DIR/ObstructionSoundness.lean"
OBSTRUCTION_BRIDGE="$SEN_DIR/ObstructionBridge.lean"
ROOT_IMPORTS="$ROOT_DIR/SocialChoiceAtlas.lean"
SCOPE_WALL="$ROOT_DIR/docs/m2_scope_wall.md"
AIM_SIGNOFF="$ROOT_DIR/docs/gates/m2/aim_signoff.md"

test -f "$OBSTRUCTION_BASIS"
test -f "$OBSTRUCTION_PROFILES"
test -f "$OBSTRUCTION_SOUNDNESS"
test -f "$OBSTRUCTION_BRIDGE"
test -f "$LIFTING_MODULE"
test -f "$SCOPE_WALL"
test -f "$AIM_SIGNOFF"

# Root-import gate (Decision 3: M2 lifting must build on every PR, not opt-in).
grep -Fq 'import SocialChoiceAtlas.Sen.ObstructionBridge' "$ROOT_IMPORTS"
grep -Fq 'import SocialChoiceAtlas.Sen.Lifting.ImpossibilityLift' "$ROOT_IMPORTS"

# Theorem-anchor gate: name and signature shape.
grep -Fq 'theorem sen_outcome_obstruction_of_' "$OBSTRUCTION_BRIDGE"
grep -Fq 'theorem sen_impossibility_from_obstruction_basis' "$OBSTRUCTION_BRIDGE"
grep -Fq 'theorem sen_impossibility_lifts' "$LIFTING_MODULE"
grep -Fq '{n m : ℕ} (_hn : 2 ≤ n) (_hm : 4 ≤ m)' "$LIFTING_MODULE"
grep -Fq '¬ SocialAcyclic F' "$LIFTING_MODULE"

# Corollary tripwire: the legacy theorem must route through the bridge theorem.
grep -Fq 'sen_impossibility_from_obstruction_basis' "$LIFTING_MODULE"

# Scope-wall structural gates (stable heading anchors over brittle prose).
grep -Eq '^## Proof Layer$' "$SCOPE_WALL"
grep -Eq '^## Witness/Audit Layer$' "$SCOPE_WALL"
grep -Eq '^## Consequence for M2$' "$SCOPE_WALL"
grep -Eq '^## Non-goals$' "$SCOPE_WALL"
# Semantic tripwire: catches accidental claim drift on the CNF-side limit.
grep -Fq 'does not upgrade the sen24 CNF atlas' "$SCOPE_WALL"

# Proof-completeness gate: the M2 obstruction bridge and compatibility lift must remain free of
# unresolved proof placeholders and leftover search-tactic stubs.
if grep -RInE '\b(sorry|admit|axiom|unsafe)\b|aesop\?|exact\?' \
    "$OBSTRUCTION_BASIS" \
    "$OBSTRUCTION_PROFILES" \
    "$OBSTRUCTION_SOUNDNESS" \
    "$OBSTRUCTION_BRIDGE" \
    "$LIFTING_MODULE"; then
  echo "M2 obstruction bridge contains unresolved proof placeholders" >&2
  exit 1
fi

cd "$ROOT_DIR"
# Narrow build target mirrors scripts/ci_phase2_smoke.sh's
# `lake build SocialChoiceAtlas.Sen.Atlas.Case11111` convention; the root
# import (checked above) ensures the default `lake build` also exercises it.
lake build SocialChoiceAtlas.Sen.ObstructionBridge
lake build SocialChoiceAtlas.Sen.Lifting.ImpossibilityLift
