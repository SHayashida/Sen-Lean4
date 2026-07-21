#!/usr/bin/env python3
"""Verify exact closure of an extracted anonymous Candidate B archive."""

import hashlib
import sys
from pathlib import Path


def main() -> int:
    root = Path(__file__).resolve().parent
    manifest = root / "m3" / "candidate_b" / "MANIFEST.sha256"
    expected = {}
    for line in manifest.read_text(encoding="utf-8").splitlines():
        digest, relative = line.split("  ", 1)
        if relative in expected:
            print("FAIL: duplicate manifest path: " + relative, file=sys.stderr)
            return 1
        expected[relative] = digest
    actual = {
        path.relative_to(root).as_posix()
        for path in root.rglob("*")
        if path.is_file() and path != manifest
    }
    if actual != set(expected):
        print("FAIL: anonymous manifest closure differs", file=sys.stderr)
        return 1
    for relative in sorted(expected):
        observed = hashlib.sha256((root / relative).read_bytes()).hexdigest()
        if observed != expected[relative]:
            print("FAIL: hash mismatch: " + relative, file=sys.stderr)
            return 1
    print("PASS: anonymous Candidate B manifest (%d files)" % len(expected))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
