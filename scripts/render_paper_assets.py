#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import re
import shutil
import subprocess
import sys
from pathlib import Path
from typing import Any

SCRIPT_DIR = Path(__file__).resolve().parent
REPO_ROOT = SCRIPT_DIR.parent

BUILD_EVIDENCE_BUNDLE = SCRIPT_DIR / "build_evidence_bundle.py"
PLOT_FRONTIER = SCRIPT_DIR / "plot_frontier.py"
PLOT_HASSE = SCRIPT_DIR / "plot_hasse_frontier.py"
GEN_PAPER_TABLES = SCRIPT_DIR / "gen_paper_tables.py"

DEFAULT_PAPER_ROOT = Path("paper")
DEFAULT_BUNDLE_ROOT = Path("results") / "paper_assets"
PAPER_ROOTS_BY_ID = {
    "m1": Path("paper"),
    "m1_5": Path("papers") / "m1_5",
}
FIGURE_NAMES = [
    "frontier_matrix.png",
    "frontier_matrix.tex",
    "frontier_boundary.png",
    "frontier_boundary.tex",
    "frontier_hasse.dot",
    "frontier_hasse.png",
    "frontier_hasse.tex",
]
TABLE_NAMES = [
    "repairs_table.tex",
    "gallery_table.tex",
    "triangulation_table.tex",
    "verification_stats_table.tex",
]


def _paper_key_for_root(paper_root: Path) -> str:
    normalized = paper_root.as_posix().strip("/")
    for paper_id, candidate in PAPER_ROOTS_BY_ID.items():
        if candidate.as_posix() == normalized:
            return paper_id
    return paper_root.name or "paper"


def _default_bundle_root_for_paper(paper_key: str) -> Path:
    if paper_key in {"m1", "paper"}:
        return DEFAULT_BUNDLE_ROOT
    return DEFAULT_BUNDLE_ROOT / paper_key


def _paper_subdir_for_bundle(*, paper_id: str | None, paper_root: Path, paper_key: str) -> str:
    if paper_id is not None:
        mapped = PAPER_ROOTS_BY_ID[paper_id]
        return mapped.as_posix()
    if not paper_root.is_absolute():
        normalized = paper_root.as_posix().strip("/")
        if normalized:
            return normalized
    if paper_key in {"m1", "paper"}:
        return DEFAULT_PAPER_ROOT.as_posix()
    return paper_key


def _run(cmd: list[str]) -> None:
    proc = subprocess.run(cmd, cwd=str(REPO_ROOT), check=False)
    if proc.returncode != 0:
        rendered = " ".join(cmd)
        raise RuntimeError(f"command failed with exit code {proc.returncode}: {rendered}")


def _load_json(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


def _assert_public_safe_text(path: Path) -> None:
    text = path.read_text(encoding="utf-8", errors="ignore")
    if "/Users/" in text:
        raise RuntimeError(f"path leak '/Users/' detected in {path}")
    if re.search(r"[A-Za-z]:\\", text):
        raise RuntimeError(f"Windows absolute path leak detected in {path}")


def _copy_file(src: Path, dst: Path) -> None:
    dst.parent.mkdir(parents=True, exist_ok=True)
    shutil.copyfile(src, dst)


def _display_path(path: Path) -> str:
    try:
        return path.relative_to(REPO_ROOT).as_posix()
    except ValueError:
        return str(path)


def _find_selected_rule_card(atlas_outdir: Path) -> Path:
    gallery_path = atlas_outdir / "gallery.json"
    if not gallery_path.exists():
        raise FileNotFoundError(f"missing gallery.json: {gallery_path}")
    gallery = _load_json(gallery_path)
    entries = gallery.get("entries", [])
    if not isinstance(entries, list) or not entries:
        raise RuntimeError("gallery.json contains no entries")
    first = entries[0]
    if not isinstance(first, dict):
        raise RuntimeError("gallery.json first entry is invalid")
    files = first.get("files", {})
    if not isinstance(files, dict):
        raise RuntimeError("gallery.json entry is missing files metadata")
    rel = files.get("rule_card_tex")
    if not isinstance(rel, str) or not rel:
        raise RuntimeError("gallery.json entry is missing files.rule_card_tex")
    path = atlas_outdir / rel
    if not path.exists():
        raise FileNotFoundError(f"missing selected rule card: {path}")
    return path


def _require_upstream_artifacts(atlas_outdir: Path) -> None:
    required = [
        atlas_outdir / "atlas.json",
        atlas_outdir / "gallery.json",
        atlas_outdir / "repair_triangulation.json",
        atlas_outdir / "maxsat_baseline.json",
    ]
    for path in required:
        if not path.exists():
            raise FileNotFoundError(
                f"missing upstream artifact for --atlas-outdir reuse: {path}"
            )
    _find_selected_rule_card(atlas_outdir)


def _render_from_existing_atlas(atlas_outdir: Path, figure_outdir: Path, table_outdir: Path) -> list[Path]:
    _require_upstream_artifacts(atlas_outdir)
    _run(
        [
            sys.executable,
            str(PLOT_FRONTIER),
            "--atlas-outdir",
            str(atlas_outdir),
            "--outdir",
            str(figure_outdir),
            "--format",
            "png",
        ]
    )
    _run(
        [
            sys.executable,
            str(PLOT_HASSE),
            "--atlas-outdir",
            str(atlas_outdir),
            "--outdir",
            str(figure_outdir),
            "--format",
            "png",
            "--include-pruned",
            "false",
            "--show",
            "status",
        ]
    )
    _run(
        [
            sys.executable,
            str(GEN_PAPER_TABLES),
            "--atlas-outdir",
            str(atlas_outdir),
            "--outdir",
            str(table_outdir),
            "--bundle-outdir",
            str(atlas_outdir.parent),
            "--tiny-bundle-outdir",
            str(atlas_outdir.parent.parent / "tiny_bundle"),
        ]
    )
    outputs = [figure_outdir / name for name in FIGURE_NAMES] + [table_outdir / name for name in TABLE_NAMES]
    for path in outputs:
        if not path.exists():
            raise FileNotFoundError(f"missing rendered paper asset: {path}")
    return outputs


def _build_bundle_if_needed(
    mode: str,
    deterministic: bool,
    *,
    bundle_root: Path,
    paper_subdir: str,
) -> Path:
    bundle_outdir = bundle_root / f"{mode}_bundle"
    cmd = [
        sys.executable,
        str(BUILD_EVIDENCE_BUNDLE),
        "--mode",
        mode,
        "--outdir",
        str(bundle_outdir),
        "--solver",
        "cadical",
        "--jobs",
        "1" if mode == "tiny" else "4",
        "--symmetry",
        "none",
        "--prune",
        "none",
        "--paper-subdir",
        paper_subdir,
    ]
    cmd.append("--deterministic" if deterministic else "--no-deterministic")
    _run(cmd)
    bundle_json = bundle_outdir / "bundle.json"
    if not bundle_json.exists():
        raise FileNotFoundError(f"missing bundle.json after bundle build: {bundle_json}")
    return bundle_outdir


def _build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        description="Render the minimal paper-facing sen24 figures/tables using existing generator scripts"
    )
    parser.add_argument("--mode", choices=["tiny", "full"], default="tiny")
    parser.add_argument(
        "--paper-id",
        choices=sorted(PAPER_ROOTS_BY_ID.keys()),
        help="Stable paper workspace identifier. Defaults to m1 behavior when omitted.",
    )
    parser.add_argument(
        "--paper-root",
        type=Path,
        help="Paper workspace root directory. Mutually exclusive with --paper-id.",
    )
    parser.add_argument(
        "--outdir",
        type=Path,
        help="Paper asset root directory; figures are written to <outdir>/figures/generated and tables to <outdir>/tables/generated. Defaults to the selected paper workspace root.",
    )
    parser.add_argument(
        "--bundle-root",
        type=Path,
        help="Root directory for auto-built evidence bundles. Defaults to results/paper_assets or a paper-specific subdirectory under it.",
    )
    parser.add_argument(
        "--atlas-outdir",
        type=Path,
        help="Reuse an existing atlas directory that already contains gallery, triangulation, baseline, and rule-card outputs",
    )
    parser.add_argument(
        "--deterministic",
        dest="deterministic",
        action="store_true",
        help="Enable deterministic upstream bundle generation (default: ON in tiny mode).",
    )
    parser.add_argument(
        "--no-deterministic",
        dest="deterministic",
        action="store_false",
        help="Disable deterministic upstream bundle generation.",
    )
    parser.set_defaults(deterministic=None)
    return parser


def main() -> None:
    args = _build_parser().parse_args()
    deterministic = True if args.deterministic is None and args.mode == "tiny" else bool(args.deterministic)
    if args.paper_id is not None and args.paper_root is not None:
        raise ValueError("--paper-id and --paper-root are mutually exclusive")

    paper_root = args.paper_root or PAPER_ROOTS_BY_ID.get(args.paper_id, DEFAULT_PAPER_ROOT)
    outdir = args.outdir or paper_root
    paper_key = args.paper_id or _paper_key_for_root(paper_root)
    bundle_root = args.bundle_root or _default_bundle_root_for_paper(paper_key)
    paper_subdir = _paper_subdir_for_bundle(
        paper_id=args.paper_id,
        paper_root=paper_root,
        paper_key=paper_key,
    )

    figure_outdir = outdir / "figures" / "generated"
    table_outdir = outdir / "tables" / "generated"
    figure_outdir.mkdir(parents=True, exist_ok=True)
    table_outdir.mkdir(parents=True, exist_ok=True)

    bundle_outdir: Path | None = None
    atlas_outdir: Path
    generated: list[Path] = []

    if args.atlas_outdir is None:
        bundle_outdir = _build_bundle_if_needed(
            args.mode,
            deterministic,
            bundle_root=bundle_root,
            paper_subdir=paper_subdir,
        )
        atlas_outdir = bundle_outdir / "atlas"
        generated.extend(_render_from_existing_atlas(atlas_outdir, figure_outdir, table_outdir))
    else:
        atlas_outdir = args.atlas_outdir
        generated.extend(_render_from_existing_atlas(atlas_outdir, figure_outdir, table_outdir))

    selected_rule_card_src = _find_selected_rule_card(atlas_outdir)
    selected_rule_card_dst = table_outdir / "selected_rule_card.tex"
    _copy_file(selected_rule_card_src, selected_rule_card_dst)
    generated.append(selected_rule_card_dst)

    for path in generated:
        if path.suffix.lower() in {".tex", ".json", ".md", ".dot"}:
            _assert_public_safe_text(path)

    print("Generated paper assets:")
    for path in sorted(generated):
        print(_display_path(path))
    print("Paper workspace:")
    print(_display_path(outdir))
    print("Upstream atlas:")
    print(_display_path(atlas_outdir))
    if bundle_outdir is not None:
        print("Bundle manifest:")
        print(_display_path(bundle_outdir / "bundle.json"))


if __name__ == "__main__":
    main()
