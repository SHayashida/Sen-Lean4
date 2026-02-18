#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import re
from pathlib import Path
from typing import Any

TABLE_SCHEMA_VERSION = 1


def _load_json(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


def _normalize_cases(atlas: dict[str, Any]) -> list[dict[str, Any]]:
    raw = atlas.get("cases", [])
    if isinstance(raw, list):
        return [c for c in raw if isinstance(c, dict)]
    if isinstance(raw, dict):
        return [c for c in raw.values() if isinstance(c, dict)]
    return []


def _tex_escape(text: str) -> str:
    escaped = text
    replacements = {
        "\\": r"\textbackslash{}",
        "&": r"\&",
        "%": r"\%",
        "$": r"\$",
        "#": r"\#",
        "_": r"\_",
        "{": r"\{",
        "}": r"\}",
        "~": r"\textasciitilde{}",
        "^": r"\textasciicircum{}",
    }
    for src, dst in replacements.items():
        escaped = escaped.replace(src, dst)
    return escaped


def _fmt_float(value: Any, digits: int = 4) -> str:
    try:
        return f"{float(value):.{digits}f}"
    except Exception:
        return "--"


def _fmt_int(value: Any) -> str:
    try:
        return str(int(value))
    except Exception:
        return "--"


def _mus_size(case: dict[str, Any]) -> str:
    mus = case.get("mus")
    if not isinstance(mus, dict):
        return "--"
    mus_axioms = mus.get("mus_axioms")
    if isinstance(mus_axioms, list):
        return str(len(mus_axioms))
    size = mus.get("size")
    return _fmt_int(size)


def _write(path: Path, lines: list[str]) -> None:
    path.write_text("\n".join(lines).rstrip() + "\n", encoding="utf-8")


def _assert_safe_text(text: str) -> None:
    if "/Users/" in text:
        raise ValueError("generated table contains disallowed '/Users/' fragment")
    if re.search(r"[A-Za-z]:\\", text):
        raise ValueError("generated table contains disallowed Windows absolute path fragment")


def _build_repairs_table(cases: list[dict[str, Any]]) -> list[str]:
    unsat_cases = sorted(
        [c for c in cases if str(c.get("status", "UNKNOWN")) == "UNSAT" and bool(c.get("solved", False))],
        key=lambda c: str(c.get("case_id", "")),
    )

    lines: list[str] = []
    lines.append(f"% table_schema_version={TABLE_SCHEMA_VERSION}")
    lines.append(r"\begin{table}[t]")
    lines.append(r"\centering")
    lines.append(r"\small")
    lines.append(r"\begin{tabular}{lrrrrr}")
    lines.append(r"\toprule")
    lines.append(r"Case & MUS & MCS$_\min$ & $|$MCS$_\min|$ & Orbit & Solved \\")
    lines.append(r"\midrule")
    if not unsat_cases:
        lines.append(r"(none) & -- & -- & -- & -- & -- \\")
    else:
        for case in unsat_cases:
            case_id = _tex_escape(str(case.get("case_id", "")))
            mus_size = _mus_size(case)
            mcs_min_size = _fmt_int(case.get("mcs_min_size"))
            mcs_min_all = case.get("mcs_min_all")
            min_count = str(len(mcs_min_all)) if isinstance(mcs_min_all, list) else "--"
            orbit = _fmt_int(case.get("orbit_size", 1))
            solved = "true" if bool(case.get("solved", False)) else "false"
            lines.append(
                f"{case_id} & {mus_size} & {mcs_min_size} & {min_count} & {orbit} & {solved} \\\\"
            )
    lines.append(r"\bottomrule")
    lines.append(r"\end{tabular}")
    lines.append(r"\caption{UNSAT repair summary from atlas outputs.}")
    lines.append(r"\label{tab:sen24-repairs}")
    lines.append(r"\end{table}")
    return lines


def _build_gallery_table(gallery_entries: list[dict[str, Any]]) -> list[str]:
    entries = sorted(gallery_entries, key=lambda e: str(e.get("case_id", "")))

    lines: list[str] = []
    lines.append(f"% table_schema_version={TABLE_SCHEMA_VERSION}")
    lines.append(r"\begin{table}[t]")
    lines.append(r"\centering")
    lines.append(r"\small")
    lines.append(r"\begin{tabular}{lrrrrl}")
    lines.append(r"\toprule")
    lines.append(r"Case & Distinct & DictMax & ConstRate & Validated & Rule Card \\")
    lines.append(r"\midrule")
    if not entries:
        lines.append(r"(none) & -- & -- & -- & -- & -- \\")
    else:
        for entry in entries:
            metrics = entry.get("metrics", {})
            files = entry.get("files", {})
            case_id = _tex_escape(str(entry.get("case_id", "")))
            distinct = _fmt_int(metrics.get("distinct_social_outcomes"))
            dict_max = _fmt_float(metrics.get("dictatorship_score_max"), digits=4)
            const_rate = _fmt_float(metrics.get("constant_function_rate"), digits=4)
            validated = "true" if bool(entry.get("model_validated", False)) else "false"
            rule_card = _tex_escape(str(files.get("rule_card_tex", "--")))
            lines.append(
                f"{case_id} & {distinct} & {dict_max} & {const_rate} & {validated} & \\texttt{{{rule_card}}} \\\\"
            )
    lines.append(r"\bottomrule")
    lines.append(r"\end{tabular}")
    lines.append(r"\caption{Selected SAT gallery entries with validation metrics.}")
    lines.append(r"\label{tab:sen24-gallery}")
    lines.append(r"\end{table}")
    return lines


def _build_triangulation_table(triangulation: dict[str, Any], baseline: dict[str, Any] | None) -> list[str]:
    raw_cases = triangulation.get("cases", [])
    tri_cases = [c for c in raw_cases if isinstance(c, dict)]
    tri_cases = sorted(tri_cases, key=lambda c: str(c.get("case_id", "")))
    baseline_case = str(baseline.get("case_id", "")) if isinstance(baseline, dict) else ""
    baseline_min = _fmt_int(baseline.get("min_repair_size")) if isinstance(baseline, dict) else "--"

    lines: list[str] = []
    lines.append(f"% table_schema_version={TABLE_SCHEMA_VERSION}")
    lines.append(r"\begin{table}[t]")
    lines.append(r"\centering")
    lines.append(r"\small")
    lines.append(r"\begin{tabular}{lrrrrr}")
    lines.append(r"\toprule")
    lines.append(r"Case & OptDrop & MCS$_\min$ & Baseline$_\min$ & SizeMatch & SetMatch \\")
    lines.append(r"\midrule")
    if not tri_cases:
        if baseline_case:
            lines.append(
                f"{_tex_escape(baseline_case)} & -- & -- & {baseline_min} & -- & -- \\\\"
            )
        else:
            lines.append(r"(none) & -- & -- & -- & -- & -- \\")
    else:
        for case in tri_cases:
            compare = case.get("compare", {})
            case_id = _tex_escape(str(case.get("case_id", "")))
            opt_drop = _fmt_int(case.get("optimum_drop_count"))
            mcs_min_size = _fmt_int(compare.get("mcs_min_size"))
            baseline_value = baseline_min if str(case.get("case_id", "")) == baseline_case else "--"
            size_match = "true" if bool(compare.get("size_match", False)) else "false"
            set_match = "true" if bool(compare.get("set_match", False)) else "false"
            lines.append(
                f"{case_id} & {opt_drop} & {mcs_min_size} & {baseline_value} & {size_match} & {set_match} \\\\"
            )
    lines.append(r"\bottomrule")
    lines.append(r"\end{tabular}")
    lines.append(
        r"\caption{Repair triangulation with a tiny MAXSAT-style sanity baseline (minimum repair size).}"
    )
    lines.append(r"\label{tab:sen24-triangulation}")
    lines.append(r"\end{table}")
    return lines


def main() -> None:
    parser = argparse.ArgumentParser(description="Generate deterministic paper table fragments from atlas artifacts")
    parser.add_argument("--atlas-outdir", type=Path, required=True, help="Atlas output directory containing atlas.json")
    parser.add_argument(
        "--outdir",
        type=Path,
        default=Path("paper") / "tables" / "generated",
        help="Output directory for generated LaTeX table fragments",
    )
    args = parser.parse_args()

    atlas_path = args.atlas_outdir / "atlas.json"
    if not atlas_path.exists():
        raise FileNotFoundError(f"missing atlas.json: {atlas_path}")

    atlas = _load_json(atlas_path)
    schema_version = atlas.get("atlas_schema_version")
    if not isinstance(schema_version, int) or schema_version < 1:
        raise ValueError("atlas_schema_version missing or invalid")

    cases = sorted(_normalize_cases(atlas), key=lambda c: str(c.get("case_id", "")))
    if int(atlas.get("cases_total", len(cases))) != len(cases):
        raise ValueError("atlas cases_total mismatch")

    gallery_entries: list[dict[str, Any]] = []
    gallery_path = args.atlas_outdir / "gallery.json"
    if gallery_path.exists():
        gallery = _load_json(gallery_path)
        raw_entries = gallery.get("entries", [])
        if isinstance(raw_entries, list):
            gallery_entries = [e for e in raw_entries if isinstance(e, dict)]

    triangulation: dict[str, Any] = {}
    tri_path = args.atlas_outdir / "repair_triangulation.json"
    if tri_path.exists():
        triangulation = _load_json(tri_path)
    baseline: dict[str, Any] | None = None
    baseline_path = args.atlas_outdir / "maxsat_baseline.json"
    if baseline_path.exists():
        baseline = _load_json(baseline_path)

    args.outdir.mkdir(parents=True, exist_ok=True)
    repairs_tex = args.outdir / "repairs_table.tex"
    gallery_tex = args.outdir / "gallery_table.tex"
    triangulation_tex = args.outdir / "triangulation_table.tex"

    repairs_lines = _build_repairs_table(cases)
    gallery_lines = _build_gallery_table(gallery_entries)
    triangulation_lines = _build_triangulation_table(triangulation, baseline)

    _write(repairs_tex, repairs_lines)
    _write(gallery_tex, gallery_lines)
    _write(triangulation_tex, triangulation_lines)

    for path in (repairs_tex, gallery_tex, triangulation_tex):
        _assert_safe_text(path.read_text(encoding="utf-8"))

    print(f"Wrote {repairs_tex}")
    print(f"Wrote {gallery_tex}")
    print(f"Wrote {triangulation_tex}")


if __name__ == "__main__":
    main()
