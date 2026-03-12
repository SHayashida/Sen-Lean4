#!/usr/bin/env python3
"""
Backward-compatible wrapper for baseline Sen24 CNF generation.

Preferred entry point:
  python3 scripts/gen_dimacs.py --n 2 --m 4 --axioms asymm,un,minlib,no_cycle3,no_cycle4 ...
"""

from __future__ import annotations

import argparse
from pathlib import Path

from gen_dimacs import DEFAULT_AXIOMS, run_generation


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument(
        "--out",
        type=Path,
        default=Path("Certificates/sen24.cnf"),
        help="Output DIMACS CNF path (default: Certificates/sen24.cnf)",
    )
    ap.add_argument(
        "--manifest-out",
        type=Path,
        default=Path("Certificates/sen24.manifest.json"),
        help="Output JSON manifest path (default: Certificates/sen24.manifest.json)",
    )
    args = ap.parse_args()

    run_generation(
        n=2,
        m=4,
        axiom_names=DEFAULT_AXIOMS[:],
        out_path=args.out,
        manifest_path=args.manifest_out,
    )
    print(f"Wrote {args.out}")
    print(f"Wrote {args.manifest_out}")


if __name__ == "__main__":
    main()
