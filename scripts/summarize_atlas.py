#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any


def resolve_atlas_path(atlas: Path | None, outdir: Path | None) -> Path:
    if atlas is not None and outdir is not None:
        expected = outdir / "atlas.json"
        if atlas.resolve() != expected.resolve():
            raise ValueError("Provide either --atlas or --outdir, or both pointing to the same file.")
        return atlas
    if atlas is not None:
        return atlas
    if outdir is not None:
        return outdir / "atlas.json"
    raise ValueError("One of --atlas or --outdir is required.")


def _atlas_cases(atlas: dict[str, Any]) -> list[dict[str, Any]]:
    raw = atlas.get("cases", [])
    if isinstance(raw, list):
        return [c for c in raw if isinstance(c, dict)]
    if isinstance(raw, dict):
        return [c for c in raw.values() if isinstance(c, dict)]
    return []


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--atlas", type=Path, default=None, help="Path to atlas.json.")
    ap.add_argument("--outdir", type=Path, default=None, help="Atlas output directory.")
    ap.add_argument(
        "--out",
        type=Path,
        default=None,
        help="Summary output path (default: <outdir>/atlas_summary.md).",
    )
    args = ap.parse_args()

    atlas_path = resolve_atlas_path(args.atlas, args.outdir)
    outdir = args.outdir if args.outdir is not None else atlas_path.parent
    out_path = args.out if args.out is not None else outdir / "atlas_summary.md"

    atlas = json.loads(atlas_path.read_text(encoding="utf-8"))
    cases = _atlas_cases(atlas)
    status_counts = dict(atlas.get("status_counts", {}))

    sat_cases = [c for c in cases if c.get("status") == "SAT"]
    unsat_cases = [c for c in cases if c.get("status") == "UNSAT"]
    case_id_by_mask = {int(c.get("mask_int", -1)): str(c.get("case_id", "")) for c in cases}

    lines: list[str] = []
    lines.append("# Atlas Summary")
    lines.append("")
    lines.append("## Headline")
    lines.append("")
    lines.append(f"- atlas_schema_version: `{atlas.get('atlas_schema_version', 'n/a')}`")
    lines.append(f"- cases_total: `{atlas.get('cases_total')}`")
    lines.append(f"- SAT: `{status_counts.get('SAT', 0)}`")
    lines.append(f"- UNSAT: `{status_counts.get('UNSAT', 0)}`")
    lines.append(f"- UNKNOWN: `{status_counts.get('UNKNOWN', 0)}`")
    lines.append("")

    lines.append("## Runtime")
    lines.append("")
    solver_info = atlas.get("solver_info", {})
    env_info = atlas.get("environment_info", {})
    lines.append(f"- solver_path: `{solver_info.get('solver_path', 'n/a')}`")
    lines.append(f"- solver_version_raw: `{solver_info.get('solver_version_raw', 'n/a')}`")
    lines.append(f"- solver_version: `{solver_info.get('solver_version', 'n/a')}`")
    lines.append(f"- solver_sha256: `{solver_info.get('solver_sha256', 'n/a')}`")
    lines.append(f"- python_version: `{env_info.get('python_version', 'n/a')}`")
    lines.append(f"- platform: `{env_info.get('platform', 'n/a')}`")
    lines.append(f"- git_commit: `{env_info.get('git_commit', 'n/a')}`")
    lines.append("")

    lines.append("## Symmetry classes")
    lines.append("")
    lines.append(f"- mode: `{atlas.get('symmetry_mode', 'none')}`")
    lines.append(f"- symmetry_unsafe_axioms: `{atlas.get('symmetry_unsafe_axioms', [])}`")
    lines.append(f"- equivalence classes: `{atlas.get('equiv_classes_total', 'n/a')}`")
    lines.append(f"- UNSAT classes: `{atlas.get('unsat_equiv_classes', 'n/a')}`")
    symmetry_check = atlas.get("symmetry_check", {})
    lines.append(
        f"- symmetry_check: enabled=`{symmetry_check.get('enabled', False)}` "
        f"checked_k=`{symmetry_check.get('checked_k', 0)}` "
        f"mismatches=`{symmetry_check.get('mismatches', 'n/a')}`"
    )
    lines.append(f"- checked_cases: `{atlas.get('checked_cases', [])}`")
    reps = atlas.get("representatives", [])
    if isinstance(reps, list) and reps:
        lines.append(f"- representatives ({len(reps)}): " + ", ".join(f"`{r}`" for r in reps))
    else:
        lines.append("- representatives: (none)")
    lines.append("")

    lines.append("## Pruning")
    lines.append("")
    prune_stats = atlas.get("prune_stats", {})
    oracle_stats = atlas.get("oracle_stats", {})
    lines.append(f"- mode: `{atlas.get('prune', 'none')}`")
    lines.append(f"- solver_calls: `{prune_stats.get('solver_calls', 'n/a')}`")
    lines.append(f"- solver_calls_avoided: `{prune_stats.get('solver_calls_avoided', 'n/a')}`")
    lines.append(f"- pruned_sat: `{prune_stats.get('pruned_sat', 'n/a')}`")
    lines.append(f"- pruned_unsat: `{prune_stats.get('pruned_unsat', 'n/a')}`")
    lines.append(f"- oracle_sat_inferred: `{oracle_stats.get('sat_inferred', 'n/a')}`")
    lines.append(f"- oracle_unsat_inferred: `{oracle_stats.get('unsat_inferred', 'n/a')}`")
    lines.append("")

    lines.append("## UNSAT cases")
    lines.append("")
    if not unsat_cases:
        lines.append("- (none)")
    else:
        for case in sorted(unsat_cases, key=lambda c: int(c.get("mask_int", 0))):
            solved = bool(case.get("solved", False))
            mus = case.get("mus", {})
            mcs = case.get("mcs", {})
            mus_axioms = mus.get("mus_axioms", []) if isinstance(mus, dict) else []
            mcs_removed = mcs.get("removed_axioms", []) if isinstance(mcs, dict) else []
            lines.append(f"- `{case.get('case_id')}` solved=`{solved}` on={case.get('axioms_on')}")
            lines.append(f"  - mus(size={len(mus_axioms)}): {mus_axioms}")
            lines.append(f"  - mcs(remove={len(mcs_removed)}): {mcs_removed}")
    lines.append("")

    lines.append("## Closest SAT cases")
    lines.append("")
    sat_sorted = sorted(
        sat_cases,
        key=lambda c: (-len(c.get("axioms_on", [])), int(c.get("mask_int", 0))),
    )
    for case in sat_sorted[:5]:
        lines.append(
            f"- `{case.get('case_id')}` on_size={len(case.get('axioms_on', []))} "
            f"solved=`{bool(case.get('solved', False))}` on={case.get('axioms_on')}"
        )
    if not sat_sorted:
        lines.append("- (none)")
    lines.append("")

    lines.append("## Class frontier")
    lines.append("")
    classes = atlas.get("equiv_classes", {})
    unsat_class_rows: list[tuple[str, dict[str, Any]]] = []
    if isinstance(classes, dict):
        for class_id, class_obj in classes.items():
            if not isinstance(class_obj, dict):
                continue
            status_map = class_obj.get("status_counts", {})
            if isinstance(status_map, dict) and int(status_map.get("UNSAT", 0)) > 0:
                unsat_class_rows.append((class_id, class_obj))
    if not unsat_class_rows:
        lines.append("- (none)")
    else:
        for class_id, class_obj in sorted(unsat_class_rows):
            lines.append(
                f"- `{class_id}` rep=`{class_obj.get('representative_case')}` "
                f"orbit={class_obj.get('orbit_size')} status={class_obj.get('status_counts')}"
            )
    lines.append("")

    lines.append("## Frontier note")
    lines.append("")
    lines.append("UNSAT case -> one-step SAT repair candidate via MCS:")
    if not unsat_cases:
        lines.append("- (none)")
    else:
        for case in sorted(unsat_cases, key=lambda c: int(c.get("mask_int", 0))):
            mcs = case.get("mcs", {})
            if not isinstance(mcs, dict) or mcs.get("status") != "ok":
                lines.append(f"- `{case.get('case_id')}`: no MCS candidate")
                continue
            sat_mask = int(mcs.get("sat_mask", -1))
            sat_case_id = case_id_by_mask.get(sat_mask, "(not in atlas cases)")
            lines.append(
                f"- `{case.get('case_id')}` --remove {mcs.get('removed_axioms')}--> "
                f"`{sat_case_id}` (`sat_mask={sat_mask}`)"
            )
    lines.append("")

    out_path.write_text("\n".join(lines).rstrip() + "\n", encoding="utf-8")
    print(f"Wrote {out_path}")


if __name__ == "__main__":
    main()
