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
    cases: list[dict[str, Any]] = list(atlas.get("cases", []))
    status_counts = atlas.get("status_counts", {})

    sat_cases = [c for c in cases if c.get("status") == "SAT"]
    unsat_cases = [c for c in cases if c.get("status") == "UNSAT"]
    case_id_by_mask = {int(c.get("mask_int", -1)): str(c.get("case_id", "")) for c in cases}

    lines: list[str] = []
    lines.append("# Atlas Summary")
    lines.append("")
    lines.append("## Headline")
    lines.append("")
    lines.append(f"- cases_total: `{atlas.get('cases_total')}`")
    lines.append(f"- SAT: `{status_counts.get('SAT', 0)}`")
    lines.append(f"- UNSAT: `{status_counts.get('UNSAT', 0)}`")
    lines.append(f"- UNKNOWN: `{status_counts.get('UNKNOWN', 0)}`")
    lines.append("")

    lines.append("## UNSAT cases")
    lines.append("")
    if not unsat_cases:
        lines.append("- (none)")
    else:
        for case in sorted(unsat_cases, key=lambda c: int(c.get("mask_int", 0))):
            mus = case.get("mus", {})
            mcs = case.get("mcs", {})
            mus_axioms = mus.get("mus_axioms", [])
            mcs_removed = mcs.get("removed_axioms", [])
            lines.append(f"- `{case.get('case_id')}` on={case.get('axioms_on')}")
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
            f"- `{case.get('case_id')}` on_size={len(case.get('axioms_on', []))} on={case.get('axioms_on')}"
        )
    if not sat_sorted:
        lines.append("- (none)")
    lines.append("")

    lines.append("## Frontier note")
    lines.append("")
    lines.append("UNSAT case -> one-step SAT repair candidate via MCS:")
    if not unsat_cases:
        lines.append("- (none)")
    else:
        for case in sorted(unsat_cases, key=lambda c: int(c.get("mask_int", 0))):
            mcs = case.get("mcs", {})
            if mcs.get("status") != "ok":
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

