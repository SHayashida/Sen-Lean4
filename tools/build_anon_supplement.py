#!/usr/bin/env python3
"""Rebuild the historically named CPP anonymous supplement for the M1.5+M3 draft.

Whitelist-based staging: only explicitly listed paths enter the archive.
After staging, an identity scan runs over every text file; any hit outside the
allowlist aborts the build. A sorted MANIFEST.sha256 is generated before
zipping. Zip entries use a fixed timestamp so rebuilds are byte-comparable.

Usage:
    python3 tools/build_anon_supplement.py \
        --lean-root  <checkout of canonical main> \
        --witness-root <checkout of witness source SHA (file-level extraction)> \
        --extras-dir tools/m1_5_m3 \
        --out cpp2027-anon-supplement.zip
"""
from __future__ import annotations

import argparse
import hashlib
import re
import shutil
import sys
import zipfile
from pathlib import Path

# ---- whitelist: (source root key, relative path, dest relative path) ----
LEAN_ITEMS = [
    "lean-toolchain",
    "lakefile.lean",
    "lake-manifest.json",
    "SocialChoiceAtlas.lean",
    "SocialChoiceAtlas",  # directory
]
WITNESS_ITEMS = [
    ("encoding", "witness/encoding"),
    ("scripts/gen_dimacs.py", "witness/tools/gen_dimacs.py"),
    (
        "results/20260401/candidate_b_minlib_granularity",
        "witness/artifacts/candidate_b_minlib_granularity",
    ),
]
EXTRA_ITEMS = [
    ("README_REPRODUCE.md", "README_REPRODUCE.md"),
    ("check_cm_witness.py", "witness/tools/check_cm_witness.py"),
]

EXCLUDE_NAMES = {"__pycache__", ".git", ".DS_Store", "AGENTS.md"}

# ---- identity scan ----
BANNED = [
    re.compile(p, re.IGNORECASE)
    for p in [
        r"hayashida",
        r"shunya",
        r"ouj\.ac\.jp",
        r"github\.com",
        r"codex",
        r"zenodo",
        r"ssrn",
        r"/home/[a-z]",
        r"/Users/",
        r"AGENTS\.md",
    ]
]
# Allowlisted exact substrings (checked before flagging a banned hit).
ALLOW = [
    "https://github.com/leanprover-community/mathlib4",  # standard dependency
    "github.com/leanprover-community/batteries",
    "github.com/leanprover-community/aesop",
    "github.com/leanprover-community/quote4",
    "github.com/leanprover-community/ProofWidgets4",
    "github.com/leanprover-community/import-graph",
    "github.com/leanprover-community/plausible",
    "github.com/leanprover-community/LeanSearchClient",
    "github.com/leanprover/lean4",
    "github.com/leanprover/std4",
    "github.com/mhuisi/lean4-cli",
]

TEXT_SUFFIXES = {
    ".lean", ".py", ".md", ".json", ".csv", ".toml", ".txt", ".cnf", ".sh", ""
}


def copy_item(src: Path, dst: Path) -> None:
    if src.is_dir():
        shutil.copytree(
            src, dst,
            ignore=shutil.ignore_patterns(*EXCLUDE_NAMES),
            dirs_exist_ok=False,
        )
    else:
        dst.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(src, dst)


def scan(stage: Path) -> list[str]:
    hits: list[str] = []
    for f in sorted(stage.rglob("*")):
        if not f.is_file() or f.suffix.lower() not in TEXT_SUFFIXES:
            continue
        try:
            text = f.read_text(encoding="utf-8")
        except UnicodeDecodeError:
            continue
        for i, line in enumerate(text.splitlines(), 1):
            probe = line
            for a in ALLOW:
                probe = probe.replace(a, "")
            for pat in BANNED:
                if pat.search(probe):
                    hits.append(f"{f.relative_to(stage)}:{i}: {pat.pattern!r}: "
                                f"{line.strip()[:100]}")
    return hits


def write_manifest(stage: Path) -> None:
    lines = []
    for f in sorted(stage.rglob("*")):
        if f.is_file() and f.name != "MANIFEST.sha256":
            h = hashlib.sha256(f.read_bytes()).hexdigest()
            lines.append(f"{h}  {f.relative_to(stage).as_posix()}")
    (stage / "MANIFEST.sha256").write_text("\n".join(lines) + "\n",
                                           encoding="utf-8")


def make_zip(stage: Path, out: Path, top: str) -> None:
    with zipfile.ZipFile(out, "w", zipfile.ZIP_DEFLATED) as z:
        for f in sorted(stage.rglob("*")):
            if not f.is_file():
                continue
            info = zipfile.ZipInfo(
                f"{top}/{f.relative_to(stage).as_posix()}",
                date_time=(1980, 1, 1, 0, 0, 0),
            )
            info.external_attr = 0o644 << 16
            z.writestr(info, f.read_bytes())


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--lean-root", type=Path, required=True)
    ap.add_argument("--witness-root", type=Path, required=True)
    ap.add_argument("--extras-dir", type=Path, required=True)
    ap.add_argument("--out", type=Path,
                    default=Path("cpp2027-anon-supplement.zip"))
    ap.add_argument("--stage", type=Path, default=Path("_anon_stage"))
    args = ap.parse_args()

    if args.stage.exists():
        shutil.rmtree(args.stage)
    args.stage.mkdir(parents=True)

    lean_dst = args.stage / "lean"
    for item in LEAN_ITEMS:
        copy_item(args.lean_root / item, lean_dst / item)
    for src_rel, dst_rel in WITNESS_ITEMS:
        copy_item(args.witness_root / src_rel, args.stage / dst_rel)
    for src_rel, dst_rel in EXTRA_ITEMS:
        copy_item(args.extras_dir / src_rel, args.stage / dst_rel)

    hits = scan(args.stage)
    if hits:
        print("IDENTITY SCAN FAILED — build aborted:", file=sys.stderr)
        for h in hits:
            print("  " + h, file=sys.stderr)
        return 1
    print("identity scan: clean")

    write_manifest(args.stage)
    nfiles = sum(1 for f in args.stage.rglob("*") if f.is_file())
    make_zip(args.stage, args.out, "cpp2027-anon-supplement")
    print(f"built {args.out} ({nfiles} files, "
          f"{args.out.stat().st_size} bytes)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
