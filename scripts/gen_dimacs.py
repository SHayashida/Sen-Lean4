#!/usr/bin/env python3
"""
Leverized DIMACS generator for the Sen base case (n=2, m=4).

Default invocation reproduces the baseline axiom set:
  asymm,un,minlib,no_cycle3,no_cycle4
"""

from __future__ import annotations

import argparse
import hashlib
import json
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from encoding.axioms import AXIOM_REGISTRY, DEFAULT_AXIOMS  # noqa: E402
from encoding.schema import Sen24Schema  # noqa: E402

CANONICAL_CATEGORY_KEYS = ["asymm", "un", "minlib", "no_cycle3", "no_cycle4"]


def _parse_axiom_names(raw: str) -> list[str]:
    names = [name.strip() for name in raw.split(",") if name.strip()]
    if not names:
        raise ValueError("At least one axiom must be selected.")
    unknown = [name for name in names if name not in AXIOM_REGISTRY]
    if unknown:
        raise ValueError(f"Unknown axiom name(s): {', '.join(unknown)}")
    if len(set(names)) != len(names):
        raise ValueError("Duplicate axiom names are not allowed.")
    return names


def _write_dimacs(path: Path, *, nvars: int, clauses: list[list[int]]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", encoding="utf-8") as f:
        f.write(f"p cnf {nvars} {len(clauses)}\n")
        for clause in clauses:
            f.write(" ".join(str(lit) for lit in clause) + " 0\n")


def _sha256(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as f:
        for chunk in iter(lambda: f.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def run_generation(
    *,
    n: int,
    m: int,
    axiom_names: list[str],
    out_path: Path,
    manifest_path: Path,
) -> dict[str, object]:
    schema = Sen24Schema(n=n, m=m, include_minlib_selectors=("minlib" in axiom_names))
    clauses: list[list[int]] = []

    category_counts = {key: 0 for key in CANONICAL_CATEGORY_KEYS}
    for axiom_name in axiom_names:
        axiom = AXIOM_REGISTRY[axiom_name]
        before = len(clauses)
        axiom.encode(schema, clauses)
        added = len(clauses) - before
        expected = axiom.expected_count(schema)
        if added != expected:
            raise RuntimeError(
                f"Axiom '{axiom_name}' emitted {added} clause(s), expected {expected}."
            )
        category_counts[axiom.category_key] += added

    _write_dimacs(out_path, nvars=schema.n_vars, clauses=clauses)
    cnf_sha256 = _sha256(out_path)
    manifest = schema.manifest_dict(
        category_counts=category_counts,
        cnf_sha256=cnf_sha256,
        nclauses=len(clauses),
        minlib_selected=("minlib" in axiom_names),
    )
    manifest_path.parent.mkdir(parents=True, exist_ok=True)
    manifest_path.write_text(json.dumps(manifest, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return manifest


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--n", type=int, default=2, help="Number of voters (only n=2 supported).")
    ap.add_argument("--m", type=int, default=4, help="Number of alternatives (only m=4 supported).")
    ap.add_argument(
        "--axioms",
        type=str,
        default=",".join(DEFAULT_AXIOMS),
        help=f"Comma-separated axiom list. Available: {','.join(AXIOM_REGISTRY.keys())}",
    )
    ap.add_argument(
        "--out",
        type=Path,
        default=Path("Certificates/sen24.cnf"),
        help="Output DIMACS CNF path.",
    )
    ap.add_argument(
        "--manifest",
        "--manifest-out",
        dest="manifest",
        type=Path,
        default=Path("Certificates/sen24.manifest.json"),
        help="Output JSON manifest path.",
    )
    args = ap.parse_args()

    axiom_names = _parse_axiom_names(args.axioms)
    run_generation(
        n=args.n,
        m=args.m,
        axiom_names=axiom_names,
        out_path=args.out,
        manifest_path=args.manifest,
    )
    print(f"Wrote {args.out}")
    print(f"Wrote {args.manifest}")


if __name__ == "__main__":
    main()

