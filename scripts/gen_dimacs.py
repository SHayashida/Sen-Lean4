#!/usr/bin/env python3
"""
Leverized DIMACS generator for finite social-choice schemas.

Default invocation still reproduces the Sen24 baseline artifact at (n=2, m=4).
For neighboring cases, the same axiom levers are instantiated against a parametric
finite schema and a generalized MINLIB witness encoding.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import shutil
import sys
import tempfile
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from encoding.axioms import AXIOM_REGISTRY, DEFAULT_AXIOMS  # noqa: E402
from encoding.schema import (  # noqa: E402
    LEGACY_MINLIB_MODE,
    PARAMETRIC_MINLIB_MODE,
    FiniteSchema,
    resolve_minlib_mode,
)

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


class ClauseBodyWriter:
    def __init__(self, body_path: Path) -> None:
        self.body_path = body_path
        self._file = body_path.open("w", encoding="utf-8")
        self._count = 0

    def append(self, clause: list[int]) -> None:
        self._file.write(" ".join(str(lit) for lit in clause) + " 0\n")
        self._count += 1

    def __len__(self) -> int:
        return self._count

    def close(self) -> None:
        self._file.close()


def _write_dimacs(path: Path, *, nvars: int, nclauses: int, body_path: Path) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", encoding="utf-8") as f:
        f.write(f"p cnf {nvars} {nclauses}\n")
        with body_path.open("r", encoding="utf-8") as body:
            shutil.copyfileobj(body, f)


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
    requested_minlib_mode: str = "auto",
) -> dict[str, object]:
    minlib_mode = resolve_minlib_mode(
        n=n,
        m=m,
        minlib_enabled=("minlib" in axiom_names),
        requested_mode=requested_minlib_mode,
    )
    schema = FiniteSchema(n=n, m=m, minlib_mode=minlib_mode)

    category_counts = {key: 0 for key in CANONICAL_CATEGORY_KEYS}
    out_path.parent.mkdir(parents=True, exist_ok=True)
    tmp_handle = tempfile.NamedTemporaryFile(
        mode="w",
        encoding="utf-8",
        delete=False,
        prefix=f"{out_path.name}.body.",
        suffix=".tmp",
        dir=str(out_path.parent),
    )
    tmp_handle.close()
    body_path = Path(tmp_handle.name)
    try:
        clauses = ClauseBodyWriter(body_path)
        try:
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
        finally:
            clauses.close()

        _write_dimacs(out_path, nvars=schema.n_vars, nclauses=len(clauses), body_path=body_path)
    finally:
        body_path.unlink(missing_ok=True)
    cnf_sha256 = _sha256(out_path)
    manifest = schema.manifest_dict(
        axiom_names=axiom_names,
        category_counts=category_counts,
        cnf_sha256=cnf_sha256,
        nclauses=len(clauses),
    )
    manifest_path.parent.mkdir(parents=True, exist_ok=True)
    manifest_path.write_text(json.dumps(manifest, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return manifest


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--n", type=int, default=2, help="Number of voters.")
    ap.add_argument("--m", type=int, default=4, help="Number of alternatives.")
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
    ap.add_argument(
        "--minlib-mode",
        choices=["auto", LEGACY_MINLIB_MODE, PARAMETRIC_MINLIB_MODE],
        default="auto",
        help=(
            "MINLIB auxiliary encoding mode. "
            "'auto' preserves the legacy Sen24 layout at (2,4) and uses the "
            "parametric witness encoding elsewhere."
        ),
    )
    args = ap.parse_args()

    axiom_names = _parse_axiom_names(args.axioms)
    run_generation(
        n=args.n,
        m=args.m,
        axiom_names=axiom_names,
        out_path=args.out,
        manifest_path=args.manifest,
        requested_minlib_mode=args.minlib_mode,
    )
    print(f"Wrote {args.out}")
    print(f"Wrote {args.manifest}")


if __name__ == "__main__":
    main()
