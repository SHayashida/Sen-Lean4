#!/usr/bin/env python3
"""
M2.1 Option D — exploratory legacy-style two-voter split encoder for (2, m).

WHAT THIS IS
------------
An isolated, exploratory encoder that generalizes the legacy Sen24
`selectors_v1` MINLIB layout from (2,4) to (2,m), with n = 2 fixed. It exists so
that the Option D *positive track* split package becomes generable at (2,5)
without touching `encoding/schema.py` and without using the parametric
`pair_selectors_v1` machinery.

OPTION D vs OPTION C — the precise distinction (do not blur)
-----------------------------------------------------------
* Option D exploratory encoder (THIS FILE) = legacy-style two-voter split, with
  NO pair selector. The liberalism layer is exposed through two direct selector
  series, exactly analogous to the legacy `sel0` / `sel1`:

      sel0(a,b) corresponds to voter 0 decisiveness  (lever decisive_voter0)
      sel1(a,b) corresponds to voter 1 decisiveness  (lever decisive_voter1)

  There are NO voter-pair selector variables and NO pair-selection clauses.

* Option C / parametric `pair_selectors_v1` (encoding/axioms/minlib_pair_selectors_v1.py)
  = voter-pair selector machinery: it allocates `var_minlib_pair(i,j)` pair
  selector variables and emits pair-selection clauses
  (`[-pair(i,j), decisive(i,·)·]`, `[-pair(i,j), decisive(j,·)·]`). That extra
  selector machinery is what risks breaking clause-multiset equivalence (≡CM) and
  is therefore explicitly NOT reused here. See
  docs/candidate_b_parametric_split_design.md.

CLAUSE STRUCTURE (mirrors encoding/axioms/minlib_selectors_v1.py)
-----------------------------------------------------------------
Let sel0(a,b), sel1(a,b) be fresh selector variables allocated immediately above
the profile/pair variables, with the same layout as legacy `selectors_v1`:

    sel0_start = n_p_vars + 1 ;  sel0(a,b) = sel0_start + pair_idx[(a,b)]
    sel1_start = sel0_start + n_pairs ;  sel1(a,b) = sel1_start + pair_idx[(a,b)]

* bundled `minlib`  (lever "minlib") emits, exactly as legacy:
    - [ sel0(a,b) for all pairs ]
    - [ sel1(a,b) for all pairs ]
    - for each profile p, each pair (a,b): [-sel0(a,b), lit0], [-sel1(a,b), lit1]
* split `decisive_voter0` emits ONLY the sel0 series:
    - [ sel0(a,b) for all pairs ]
    - for each profile p, each pair (a,b): [-sel0(a,b), lit0]
* split `decisive_voter1` emits ONLY the sel1 series:
    - [ sel1(a,b) for all pairs ]
    - for each profile p, each pair (a,b): [-sel1(a,b), lit1]

where lit0 = var_p(p,a,b) if pref0(p,a,b) else var_p(p,b,a) (and lit1 with
voter 1). Hence the bundled `minlib` clause multiset equals the union of the
`decisive_voter0` and `decisive_voter1` clause multisets over identical
variables, so an identity variable renaming witnesses ≡CM at (2,m) — exactly as
in the M1.5 base case.

Shared levers (asymm, un, no_cycle3, no_cycle4) are produced by the existing
`encoding.axioms` encoders on a `disabled`-mode schema; they use only the
profile/pair variables and never the selector region.

SCOPE
-----
* n = 2 only (raises otherwise). This is the (2,m) positive track.
* No pair-selector lever is accepted (raises). This encoder cannot express
  Option C.
* This is exploratory feasibility code under scripts/exploration/candidate_b/.
  It does not modify encoding/schema.py and is not promoted to scripts/.
"""

from __future__ import annotations

import hashlib
import json
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[3]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from encoding.axioms import AXIOM_REGISTRY  # noqa: E402
from encoding.schema import FiniteSchema  # noqa: E402

ENCODING_LABEL = "option_d_legacy_two_series_v0"

SHARED_LEVERS = {"asymm", "un", "no_cycle3", "no_cycle4"}
LIBERALISM_LEVERS = {"minlib", "decisive_voter0", "decisive_voter1"}
KNOWN_LEVERS = SHARED_LEVERS | LIBERALISM_LEVERS
# Levers that would pull in Option C / pair-selector machinery. Rejected here.
FORBIDDEN_OPTION_C_LEVERS = {"minlib_pair", "pair_selector", "selected_decisive_left", "selected_decisive_right"}

CANONICAL_ORDER = ["asymm", "un", "minlib", "decisive_voter0", "decisive_voter1", "no_cycle3", "no_cycle4"]


class _SelectorLayout:
    """Legacy-style sel0/sel1 variable allocation above the profile/pair vars."""

    def __init__(self, schema: FiniteSchema) -> None:
        self.schema = schema
        self.sel0_start = schema.n_p_vars + 1
        self.sel1_start = self.sel0_start + schema.n_pairs
        self.sel1_end = self.sel1_start + schema.n_pairs - 1

    def sel0(self, a: int, b: int) -> int:
        return self.sel0_start + self.schema.pair_idx[(a, b)]

    def sel1(self, a: int, b: int) -> int:
        return self.sel1_start + self.schema.pair_idx[(a, b)]


def _lit_for_voter(schema: FiniteSchema, p: int, a: int, b: int, voter: int) -> int:
    return schema.var_p(p, a, b) if schema.prefers(p, voter, a, b) else schema.var_p(p, b, a)


def _emit_decisive_series(
    schema: FiniteSchema, layout: _SelectorLayout, voter: int, out: list[list[int]]
) -> None:
    sel = layout.sel0 if voter == 0 else layout.sel1
    out.append([sel(a, b) for (a, b) in schema.pairs])
    for p in range(schema.n_profiles):
        for a, b in schema.pairs:
            out.append([-sel(a, b), _lit_for_voter(schema, p, a, b, voter)])


def _emit_bundled_minlib(schema: FiniteSchema, layout: _SelectorLayout, out: list[list[int]]) -> None:
    # Legacy two-series minlib: both selector "at-least-one" clauses, then both
    # implication series, exactly as encoding/axioms/minlib_selectors_v1.py.
    out.append([layout.sel0(a, b) for (a, b) in schema.pairs])
    out.append([layout.sel1(a, b) for (a, b) in schema.pairs])
    for p in range(schema.n_profiles):
        for a, b in schema.pairs:
            out.append([-layout.sel0(a, b), _lit_for_voter(schema, p, a, b, 0)])
            out.append([-layout.sel1(a, b), _lit_for_voter(schema, p, a, b, 1)])


def build_clauses(n: int, m: int, axioms: list[str]) -> tuple[list[list[int]], int, dict[str, int]]:
    """Build the clause list, nvars, and per-lever clause counts for a package."""
    if n != 2:
        raise ValueError(
            f"Option D exploratory encoder is two-voter only (n=2); got n={n}. "
            "Voter-dimension generalization (n>2) is the Option C boundary track."
        )
    bad = [ax for ax in axioms if ax in FORBIDDEN_OPTION_C_LEVERS]
    if bad:
        raise ValueError(f"Option D rejects pair-selector levers (Option C only): {bad}")
    unknown = [ax for ax in axioms if ax not in KNOWN_LEVERS]
    if unknown:
        raise ValueError(f"unknown lever(s) for Option D encoder: {unknown}")
    if len(set(axioms)) != len(axioms):
        raise ValueError("duplicate levers are not allowed")

    schema = FiniteSchema(n=2, m=m, minlib_mode="disabled")
    layout = _SelectorLayout(schema)

    clauses: list[list[int]] = []
    per_lever: dict[str, int] = {}
    for lever in CANONICAL_ORDER:
        if lever not in axioms:
            continue
        before = len(clauses)
        if lever in SHARED_LEVERS:
            AXIOM_REGISTRY[lever].encode(schema, clauses)
        elif lever == "minlib":
            _emit_bundled_minlib(schema, layout, clauses)
        elif lever == "decisive_voter0":
            _emit_decisive_series(schema, layout, 0, clauses)
        elif lever == "decisive_voter1":
            _emit_decisive_series(schema, layout, 1, clauses)
        per_lever[lever] = len(clauses) - before

    nvars = max((abs(lit) for clause in clauses for lit in clause), default=0)
    return clauses, nvars, per_lever


def _sha256(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as f:
        for chunk in iter(lambda: f.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def generate_package(
    *, n: int, m: int, axiom_names: list[str], out_path: Path, manifest_path: Path
) -> dict[str, object]:
    """Generate a DIMACS CNF + manifest for one Option D package. Returns counts."""
    clauses, nvars, per_lever = build_clauses(n, m, axiom_names)
    out_path.parent.mkdir(parents=True, exist_ok=True)
    with out_path.open("w", encoding="utf-8") as f:
        f.write(f"p cnf {nvars} {len(clauses)}\n")
        for clause in clauses:
            f.write(" ".join(str(lit) for lit in clause) + " 0\n")

    manifest = {
        "encoding": ENCODING_LABEL,
        "n": n,
        "m": m,
        "axioms": list(axiom_names),
        "nvars": nvars,
        "nclauses": len(clauses),
        "per_lever_clause_counts": per_lever,
        "cnf_sha256": _sha256(out_path),
        "uses_pair_selectors": False,
        "note": (
            "Legacy-style two-voter (2,m) split; sel0/sel1 direct series; "
            "no voter-pair selector variables or pair-selection clauses."
        ),
    }
    manifest_path.parent.mkdir(parents=True, exist_ok=True)
    manifest_path.write_text(json.dumps(manifest, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return {
        "cnf": out_path,
        "nvars": nvars,
        "nclauses": len(clauses),
        "encoding": ENCODING_LABEL,
        "per_lever_clause_counts": per_lever,
    }
