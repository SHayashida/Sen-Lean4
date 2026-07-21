#!/usr/bin/env python3
"""Verify the Candidate B package SHA-256 manifest and exact closure."""

import hashlib
import sys
from pathlib import Path


def main() -> int:
    package = Path(__file__).resolve().parent
    manifest_path = package / "MANIFEST.sha256"
    if not manifest_path.is_file():
        print("FAIL: MANIFEST.sha256 is missing", file=sys.stderr)
        return 1
    expected = {}
    for line in manifest_path.read_text(encoding="utf-8").splitlines():
        digest, relative = line.split("  ", 1)
        if relative in expected:
            print("FAIL: duplicate manifest path: " + relative, file=sys.stderr)
            return 1
        expected[relative] = digest
    actual = {
        path.relative_to(package).as_posix()
        for path in package.rglob("*")
        if path.is_file() and path != manifest_path
    }
    if actual != set(expected):
        print("FAIL: manifest closure differs", file=sys.stderr)
        return 1
    for relative in sorted(expected):
        digest = hashlib.sha256((package / relative).read_bytes()).hexdigest()
        if digest != expected[relative]:
            print("FAIL: hash mismatch: " + relative, file=sys.stderr)
            return 1
    print("PASS: Candidate B manifest (%d files)" % len(expected))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
