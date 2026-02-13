#!/usr/bin/env python3
from __future__ import annotations

import argparse
import base64
import json
from pathlib import Path
from typing import Any


def _load_json(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


def _group_runs(eval_obj: dict[str, Any]) -> tuple[list[str], dict[str, list[dict[str, Any]]]]:
    config_order = [str(cfg) for cfg in eval_obj.get("configs", [])]
    grouped: dict[str, list[dict[str, Any]]] = {cfg: [] for cfg in config_order}
    for run in eval_obj.get("runs", []):
        if not isinstance(run, dict):
            continue
        config_id = str(run.get("config_id", ""))
        metrics = run.get("run_metrics")
        if not isinstance(metrics, dict):
            continue
        if config_id not in grouped:
            grouped[config_id] = []
            config_order.append(config_id)
        grouped[config_id].append(metrics)
    return config_order, grouped


def _write_placeholder_png(path: Path) -> None:
    one_pixel_png = base64.b64decode(
        "iVBORw0KGgoAAAANSUhEUgAAAAEAAAABCAQAAAC1HAwCAAAAC0lEQVR42mP8/x8AAwMCAO3Zf90AAAAASUVORK5CYII="
    )
    path.write_bytes(one_pixel_png)


def _runtime_boxplot(config_order: list[str], grouped: dict[str, list[dict[str, Any]]], out_path: Path) -> None:
    import matplotlib.pyplot as plt

    data = [[float(m.get("wall_time_sec", 0.0)) for m in grouped.get(cfg, [])] for cfg in config_order]
    fig, ax = plt.subplots(figsize=(9, 4.5))
    ax.boxplot(data, labels=config_order)
    ax.set_title("Runtime by config")
    ax.set_xlabel("config_id")
    ax.set_ylabel("wall_time_sec")
    ax.grid(axis="y", alpha=0.25)
    fig.tight_layout()
    fig.savefig(out_path, dpi=160)
    plt.close(fig)


def _solved_vs_pruned(config_order: list[str], grouped: dict[str, list[dict[str, Any]]], out_path: Path) -> None:
    import matplotlib.pyplot as plt

    solved_true_means: list[float] = []
    solved_false_means: list[float] = []
    for cfg in config_order:
        rows = grouped.get(cfg, [])
        if not rows:
            solved_true_means.append(0.0)
            solved_false_means.append(0.0)
            continue
        solved_true_means.append(sum(float(r.get("solved_true_count", 0.0)) for r in rows) / len(rows))
        solved_false_means.append(sum(float(r.get("solved_false_count", 0.0)) for r in rows) / len(rows))

    x = list(range(len(config_order)))
    fig, ax = plt.subplots(figsize=(9, 4.5))
    ax.bar(x, solved_true_means, label="solved_true")
    ax.bar(x, solved_false_means, bottom=solved_true_means, label="solved_false (pruned/inferred)")
    ax.set_xticks(x)
    ax.set_xticklabels(config_order)
    ax.set_title("Solved vs pruned per config")
    ax.set_xlabel("config_id")
    ax.set_ylabel("cases")
    ax.legend()
    ax.grid(axis="y", alpha=0.25)
    fig.tight_layout()
    fig.savefig(out_path, dpi=160)
    plt.close(fig)


def _symmetry_reduction(config_order: list[str], grouped: dict[str, list[dict[str, Any]]], out_path: Path) -> None:
    import matplotlib.pyplot as plt

    equiv_means: list[float] = []
    orbit_means: list[float] = []
    orbit_max_means: list[float] = []

    for cfg in config_order:
        rows = grouped.get(cfg, [])
        if not rows:
            equiv_means.append(0.0)
            orbit_means.append(0.0)
            orbit_max_means.append(0.0)
            continue
        equiv_means.append(sum(float(r.get("equiv_classes_total", 0.0)) for r in rows) / len(rows))
        orbit_means.append(
            sum(float(r.get("orbit_size_stats", {}).get("mean", 0.0)) for r in rows) / len(rows)
        )
        orbit_max_means.append(
            sum(float(r.get("orbit_size_stats", {}).get("max", 0.0)) for r in rows) / len(rows)
        )

    x = list(range(len(config_order)))
    fig, ax1 = plt.subplots(figsize=(9, 4.5))
    bars = ax1.bar(x, equiv_means, label="equiv_classes_total (mean)")
    ax1.set_xlabel("config_id")
    ax1.set_ylabel("equiv classes")
    ax1.set_xticks(x)
    ax1.set_xticklabels(config_order)
    ax1.grid(axis="y", alpha=0.25)

    ax2 = ax1.twinx()
    ax2.plot(x, orbit_means, marker="o", linestyle="-", label="orbit_size_mean")
    ax2.plot(x, orbit_max_means, marker="s", linestyle="--", label="orbit_size_max")
    ax2.set_ylabel("orbit size")

    handles = [bars]
    labels = ["equiv_classes_total (mean)"]
    for line in ax2.get_lines():
        handles.append(line)
    labels.extend(["orbit_size_mean", "orbit_size_max"])
    ax1.legend(handles, labels, loc="best")
    ax1.set_title("Symmetry reduction statistics")

    fig.tight_layout()
    fig.savefig(out_path, dpi=160)
    plt.close(fig)


def main() -> None:
    ap = argparse.ArgumentParser(description="Plot paper-ready evaluation figures from eval.json")
    ap.add_argument("--eval-json", type=Path, required=True, help="Path to eval.json produced by scripts/eval_atlas.py")
    ap.add_argument(
        "--outdir",
        type=Path,
        default=None,
        help="Figure output directory (default: <eval_json_dir>/figures)",
    )
    ap.add_argument(
        "--figures",
        type=str,
        default="runtime_boxplot,solved_vs_pruned,symmetry_reduction",
        help="CSV subset: runtime_boxplot,solved_vs_pruned,symmetry_reduction",
    )
    args = ap.parse_args()

    eval_obj = _load_json(args.eval_json)
    config_order, grouped = _group_runs(eval_obj)
    if not config_order:
        raise SystemExit("No runs found in eval.json")

    outdir = args.outdir if args.outdir is not None else args.eval_json.parent / "figures"
    outdir.mkdir(parents=True, exist_ok=True)

    requested = [f.strip() for f in args.figures.split(",") if f.strip()]
    valid = {"runtime_boxplot", "solved_vs_pruned", "symmetry_reduction"}
    unknown = [name for name in requested if name not in valid]
    if unknown:
        raise SystemExit(f"Unknown figure names: {', '.join(unknown)}")

    has_matplotlib = True
    try:
        import matplotlib

        matplotlib.use("Agg")
        import matplotlib.pyplot as plt  # noqa: F401
    except ImportError:
        has_matplotlib = False

    written: list[Path] = []
    if has_matplotlib:
        for name in requested:
            out_path = outdir / f"{name}.png"
            if name == "runtime_boxplot":
                _runtime_boxplot(config_order, grouped, out_path)
            elif name == "solved_vs_pruned":
                _solved_vs_pruned(config_order, grouped, out_path)
            elif name == "symmetry_reduction":
                _symmetry_reduction(config_order, grouped, out_path)
            written.append(out_path)
    else:
        for name in requested:
            out_path = outdir / f"{name}.png"
            _write_placeholder_png(out_path)
            written.append(out_path)
        print("warning: matplotlib is unavailable; wrote placeholder PNG files instead.")

    for path in written:
        print(f"Wrote {path}")


if __name__ == "__main__":
    main()
