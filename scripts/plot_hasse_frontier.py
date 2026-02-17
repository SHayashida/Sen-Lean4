#!/usr/bin/env python3
from __future__ import annotations

import argparse
import base64
import json
import shutil
import subprocess
from pathlib import Path
from typing import Any


def _load_json(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


def _normalize_cases(atlas: dict[str, Any]) -> list[dict[str, Any]]:
    raw = atlas.get("cases", [])
    if isinstance(raw, list):
        return [c for c in raw if isinstance(c, dict)]
    if isinstance(raw, dict):
        return [c for c in raw.values() if isinstance(c, dict)]
    return []


def _status_for_label(case: dict[str, Any]) -> str:
    solved = bool(case.get("solved", False))
    status = str(case.get("status", "UNKNOWN"))
    if solved:
        return status
    derived = status
    pruned_by = case.get("pruned_by")
    if isinstance(pruned_by, dict):
        derived = str(pruned_by.get("derived_status", status))
    return f"PRUNED({derived})"


def _validate_atlas(atlas: dict[str, Any]) -> list[dict[str, Any]]:
    schema = atlas.get("atlas_schema_version")
    if not isinstance(schema, int) or schema < 1:
        raise ValueError("atlas_schema_version missing or invalid")

    cases = sorted(_normalize_cases(atlas), key=lambda c: str(c.get("case_id", "")))
    if not cases:
        raise ValueError("atlas contains no cases")

    cases_total = int(atlas.get("cases_total", len(cases)))
    if cases_total != len(cases):
        raise ValueError(f"cases_total mismatch: header={cases_total} actual={len(cases)}")
    return cases


def _is_cover(mask_a: int, mask_b: int, masks: list[int]) -> bool:
    if mask_a == mask_b:
        return False
    if (mask_a & mask_b) != mask_a:
        return False
    for mask_mid in masks:
        if mask_mid in {mask_a, mask_b}:
            continue
        if (mask_a & mask_mid) == mask_a and (mask_mid & mask_b) == mask_mid:
            return False
    return True


def _escape_dot_label(text: str) -> str:
    return text.replace("\\", "\\\\").replace("\"", "\\\"")


def _write_placeholder(path: Path, fmt: str) -> None:
    if fmt == "png":
        one_pixel_png = base64.b64decode(
            "iVBORw0KGgoAAAANSUhEUgAAAAEAAAABCAQAAAC1HAwCAAAAC0lEQVR42mP8/x8AAwMCAO3Zf90AAAAASUVORK5CYII="
        )
        path.write_bytes(one_pixel_png)
        return
    if fmt == "svg":
        path.write_text(
            "<svg xmlns='http://www.w3.org/2000/svg' width='1' height='1' viewBox='0 0 1 1'></svg>\n",
            encoding="utf-8",
        )
        return
    if fmt == "pdf":
        path.write_bytes(
            b"%PDF-1.1\n1 0 obj<<>>endobj\n2 0 obj<<>>endobj\ntrailer<<>>\n%%EOF\n"
        )
        return
    raise ValueError(f"unsupported placeholder format: {fmt}")


def _render_dot(dot_path: Path, image_path: Path, fmt: str) -> None:
    dot_bin = shutil.which("dot")
    if dot_bin is None:
        _write_placeholder(image_path, fmt)
        return
    proc = subprocess.run(
        [dot_bin, f"-T{fmt}", str(dot_path), "-o", str(image_path)],
        capture_output=True,
        text=True,
        check=False,
    )
    if proc.returncode != 0:
        _write_placeholder(image_path, fmt)


def build_hasse_dot(
    *,
    atlas_path: Path,
    outdir: Path,
    image_format: str,
    include_pruned: bool,
    show: str,
) -> tuple[Path, Path]:
    atlas = _load_json(atlas_path)
    cases = _validate_atlas(atlas)

    selected = [c for c in cases if include_pruned or bool(c.get("solved", False))]
    if not selected:
        raise ValueError("no cases selected for Hasse graph")

    selected = sorted(selected, key=lambda c: str(c.get("case_id", "")))
    masks = [int(c.get("mask_int", -1)) for c in selected]
    if any(mask < 0 for mask in masks):
        raise ValueError("all selected cases must have non-negative mask_int")

    case_by_mask = {int(c["mask_int"]): c for c in selected}
    if len(case_by_mask) != len(selected):
        raise ValueError("selected cases contain duplicate mask_int")

    edges: list[tuple[str, str]] = []
    for mask_a in masks:
        for mask_b in masks:
            if _is_cover(mask_a, mask_b, masks):
                case_a = case_by_mask[mask_a]
                case_b = case_by_mask[mask_b]
                edges.append((str(case_a["case_id"]), str(case_b["case_id"])))
    edges = sorted(set(edges))

    outdir.mkdir(parents=True, exist_ok=True)
    dot_path = outdir / "frontier_hasse.dot"
    image_path = outdir / f"frontier_hasse.{image_format}"

    lines: list[str] = []
    lines.append("digraph frontier_hasse {")
    lines.append("  rankdir=BT;")
    lines.append("  node [shape=box, style=\"rounded,filled\", fillcolor=white];")

    for case in selected:
        case_id = str(case["case_id"])
        label_lines = [case_id]
        label_lines.append(f"solved={str(bool(case.get('solved', False))).lower()}")
        if show in {"status", "orbit"}:
            label_lines.append(f"status={_status_for_label(case)}")
        if show == "orbit" and case.get("orbit_size") is not None:
            label_lines.append(f"orbit={case.get('orbit_size')}")
        label = "\\n".join(_escape_dot_label(x) for x in label_lines)

        status_key = _status_for_label(case)
        if status_key.startswith("UNSAT"):
            fillcolor = "mistyrose"
        elif status_key.startswith("SAT"):
            fillcolor = "honeydew"
        elif status_key.startswith("PRUNED"):
            fillcolor = "lightgray"
        else:
            fillcolor = "white"

        lines.append(f'  "{case_id}" [label="{label}", fillcolor="{fillcolor}"];')

    for src, dst in edges:
        lines.append(f'  "{src}" -> "{dst}";')
    lines.append("}")
    dot_path.write_text("\n".join(lines).rstrip() + "\n", encoding="utf-8")

    _render_dot(dot_path, image_path, image_format)
    return dot_path, image_path


def main() -> None:
    ap = argparse.ArgumentParser(description="Generate deterministic Hasse/poset frontier visualization from atlas.json")
    ap.add_argument("--atlas-outdir", type=Path, required=True, help="Directory containing atlas.json")
    ap.add_argument(
        "--outdir",
        type=Path,
        default=Path("paper") / "figures" / "generated",
        help="Output directory for DOT and rendered image",
    )
    ap.add_argument("--format", dest="image_format", choices=["png", "pdf", "svg"], default="png")
    ap.add_argument("--include-pruned", choices=["true", "false"], default="false")
    ap.add_argument("--show", choices=["status", "orbit"], default="status")
    args = ap.parse_args()

    atlas_path = args.atlas_outdir / "atlas.json"
    if not atlas_path.exists():
        raise FileNotFoundError(f"missing atlas.json: {atlas_path}")

    dot_path, image_path = build_hasse_dot(
        atlas_path=atlas_path,
        outdir=args.outdir,
        image_format=args.image_format,
        include_pruned=(args.include_pruned == "true"),
        show=args.show,
    )
    print(f"Wrote {dot_path}")
    print(f"Wrote {image_path}")


if __name__ == "__main__":
    main()
