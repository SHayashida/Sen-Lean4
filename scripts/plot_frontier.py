#!/usr/bin/env python3
from __future__ import annotations

import argparse
import base64
import json
from collections import Counter
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


def _status_label(case: dict[str, Any]) -> str:
    status = str(case.get("status", "UNKNOWN"))
    solved = bool(case.get("solved", False))
    if not solved and status in {"SAT", "UNSAT"}:
        return "PRUNED"
    if status == "SAT":
        return "SAT"
    if status == "UNSAT":
        return "UNSAT"
    return "UNKNOWN"


def _mus_size(case: dict[str, Any]) -> int | None:
    mus = case.get("mus")
    if not isinstance(mus, dict):
        return None
    axioms = mus.get("mus_axioms")
    if isinstance(axioms, list):
        return len(axioms)
    size = mus.get("size")
    if isinstance(size, int):
        return size
    return None


def _matrix(values: list[int], cols: int = 8, fill: int = 0) -> list[list[int]]:
    rows = (len(values) + cols - 1) // cols
    padded = list(values) + [fill] * (rows * cols - len(values))
    return [padded[r * cols : (r + 1) * cols] for r in range(rows)]


def _write_placeholder_png(path: Path) -> None:
    one_pixel_png = base64.b64decode(
        "iVBORw0KGgoAAAANSUhEUgAAAAEAAAABCAQAAAC1HAwCAAAAC0lEQVR42mP8/x8AAwMCAO3Zf90AAAAASUVORK5CYII="
    )
    path.write_bytes(one_pixel_png)


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


def plot_frontier(atlas_path: Path, outdir: Path, fmt: str) -> tuple[Path, Path]:
    atlas = _load_json(atlas_path)
    cases = _validate_atlas(atlas)

    labels = [_status_label(c) for c in cases]
    code_map = {"SAT": 0, "UNSAT": 1, "PRUNED": 2, "UNKNOWN": 3}
    codes = [code_map[label] for label in labels]

    outdir.mkdir(parents=True, exist_ok=True)
    matrix_path = outdir / f"frontier_matrix.{fmt}"
    boundary_path = outdir / f"frontier_boundary.{fmt}"

    has_matplotlib = True
    try:
        import matplotlib

        matplotlib.use("Agg")
        import matplotlib.pyplot as plt
    except ImportError:
        has_matplotlib = False

    if not has_matplotlib:
        if fmt != "png":
            raise RuntimeError("matplotlib is required for PDF output")
        _write_placeholder_png(matrix_path)
        _write_placeholder_png(boundary_path)
        return matrix_path, boundary_path

    # Figure 1: compact matrix view
    mat = _matrix(codes, cols=8, fill=code_map["UNKNOWN"])
    fig1, ax1 = plt.subplots(figsize=(10, 3.6))
    im = ax1.imshow(mat, aspect="auto", interpolation="nearest")
    ax1.set_title("Frontier matrix by case order")
    ax1.set_xlabel("column index")
    ax1.set_ylabel("row index")

    cbar = fig1.colorbar(im, ax=ax1)
    cbar.set_ticks([0, 1, 2, 3])
    cbar.set_ticklabels(["SAT", "UNSAT", "PRUNED", "UNKNOWN"])

    fig1.tight_layout()
    fig1.savefig(matrix_path, dpi=160)
    plt.close(fig1)

    # Figure 2: boundary-focused scatter with MUS annotations
    indices = list(range(len(cases)))
    popcounts = [str(c.get("mask_bits", "")).count("1") for c in cases]
    fig2, ax2 = plt.subplots(figsize=(11, 4.2))

    scatter = ax2.scatter(indices, popcounts, c=codes)
    ax2.set_title("Frontier boundary view (UNSAT annotated)")
    ax2.set_xlabel("case index (lexicographic case_id)")
    ax2.set_ylabel("enabled axioms (popcount)")

    unsat_points = [
        (idx, c)
        for idx, c in enumerate(cases)
        if _status_label(c) == "UNSAT"
    ]
    for idx, case in unsat_points:
        mus_size = _mus_size(case)
        label = "mus=?" if mus_size is None else f"mus={mus_size}"
        ax2.annotate(
            label,
            (idx, popcounts[idx]),
            textcoords="offset points",
            xytext=(0, 8),
            ha="center",
            fontsize=8,
        )
        ax2.scatter([idx], [popcounts[idx]], marker="o", s=80, facecolors="none")

    pruned_points = [idx for idx, c in enumerate(cases) if _status_label(c) == "PRUNED"]
    if pruned_points:
        ax2.scatter(
            pruned_points,
            [popcounts[idx] for idx in pruned_points],
            marker="x",
            linewidths=1.2,
            label="pruned/inferred",
        )

    status_counts = Counter(labels)
    ax2.text(
        0.01,
        0.02,
        f"SAT={status_counts.get('SAT', 0)} UNSAT={status_counts.get('UNSAT', 0)} "
        f"PRUNED={status_counts.get('PRUNED', 0)} UNKNOWN={status_counts.get('UNKNOWN', 0)}",
        transform=ax2.transAxes,
        fontsize=8,
    )

    if pruned_points:
        ax2.legend(loc="upper right")

    fig2.colorbar(scatter, ax=ax2, ticks=[0, 1, 2, 3], label="status code")
    fig2.tight_layout()
    fig2.savefig(boundary_path, dpi=160)
    plt.close(fig2)

    return matrix_path, boundary_path


def main() -> None:
    ap = argparse.ArgumentParser(description="Generate minimal frontier figures from atlas.json")
    ap.add_argument("--atlas-outdir", type=Path, required=True, help="Directory containing atlas.json")
    ap.add_argument(
        "--outdir",
        type=Path,
        default=Path("paper") / "figures" / "generated",
        help="Output directory for figures",
    )
    ap.add_argument("--format", choices=["png", "pdf"], default="png")
    args = ap.parse_args()

    atlas_path = args.atlas_outdir / "atlas.json"
    if not atlas_path.exists():
        raise FileNotFoundError(f"missing atlas.json: {atlas_path}")

    matrix_path, boundary_path = plot_frontier(atlas_path, args.outdir, args.format)
    print(f"Wrote {matrix_path}")
    print(f"Wrote {boundary_path}")


if __name__ == "__main__":
    main()
