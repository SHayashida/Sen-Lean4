#!/usr/bin/env python3
"""Build Step 1 base-case repair triples for the repair-liftability experiment.

For each UNSAT axiom package A in the base case (n=2, m=4), enumerate all
inclusion-minimal repairs R_i and materialize each distinct triple (A, R_i, A\R_i)
as a durable artifact.

Usage (from repo root):
    python3 scripts/build_base_repair_triples.py \\
        --date 20260401 \\
        --outdir results/20260401/repair_liftability

See docs/experiment_protocol_repair_liftability.md for Step 1 specification.
See docs/no_cycle_interpretation_note.md for scope restrictions on no_cycle3/no_cycle4.
"""
from __future__ import annotations

import argparse
import json
import sys
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

SCRIPT_DIR = Path(__file__).resolve().parent
REPO_ROOT = SCRIPT_DIR.parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

from enumerate_repairs import (  # noqa: E402
    _enumerate_case_repairs,
    _case_lookup,
    _normalize_cases,
    _validate_repairs,
)

# ── canonical lever family ────────────────────────────────────────────────────
CANONICAL_FAMILY: list[str] = ["asymm", "un", "minlib", "no_cycle3", "no_cycle4"]

SCOPE_NOTE = (
    "no_cycle3 and no_cycle4 are treated as local-rationality approximations, "
    "not full SocialAcyclic. Candidate A evidence is valid only within that "
    "restricted local-rationality family. "
    "See docs/no_cycle_interpretation_note.md and docs/axiom_semantics_scaling.md."
)

DEFAULT_ATLAS = REPO_ROOT / "results" / "jar_full_atlas" / "atlas.json"


# ── helpers ───────────────────────────────────────────────────────────────────

def _canonical_key(axioms: list[str]) -> str:
    """Return a deterministic string key for a lever subset.

    Members are sorted by their position in CANONICAL_FAMILY so that the
    same logical subset always maps to the same key regardless of input order.
    """
    order = {ax: i for i, ax in enumerate(CANONICAL_FAMILY)}
    sorted_axioms = sorted(axioms, key=lambda ax: order[ax])
    return "+".join(sorted_axioms) if sorted_axioms else "(empty)"


def _canonical_list(axioms: list[str]) -> list[str]:
    """Return axioms sorted by CANONICAL_FAMILY order."""
    order = {ax: i for i, ax in enumerate(CANONICAL_FAMILY)}
    return sorted(axioms, key=lambda ax: order[ax])


def _load_json(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


def _write_json(path: Path, payload: dict[str, Any]) -> None:
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


# ── core builder ─────────────────────────────────────────────────────────────

def build_triples(
    *,
    atlas_path: Path,
    date_str: str,
) -> dict[str, Any]:
    """Load the base-case atlas and build all (A, R_i, A\\R_i) triples."""

    atlas = _load_json(atlas_path)
    axiom_universe: list[str] = list(atlas.get("axiom_universe", []))
    if axiom_universe != CANONICAL_FAMILY:
        raise ValueError(
            f"atlas axiom_universe {axiom_universe} does not match expected "
            f"CANONICAL_FAMILY {CANONICAL_FAMILY}. "
            "Refusing to proceed to avoid silently mis-keying triples."
        )

    cases = _normalize_cases(atlas)
    case_by_mask = _case_lookup(cases)
    width = len(axiom_universe)

    unsat_cases = [c for c in cases if str(c.get("status", "")) == "UNSAT"]
    if not unsat_cases:
        raise RuntimeError("No UNSAT cases found in atlas.")
    for c in unsat_cases:
        if not bool(c.get("solved", False)):
            raise RuntimeError(
                f"UNSAT case {c.get('case_id')} has solved=false; "
                "run full atlas solve before building repair triples."
            )

    triples: list[dict[str, Any]] = []
    seen_keys: set[tuple[str, str]] = set()

    per_package: list[dict[str, Any]] = []

    for case in sorted(unsat_cases, key=lambda c: str(c.get("case_id", ""))):
        case_id = str(case["case_id"])
        unsat_mask = int(case["mask_int"])
        base_axioms_on = _canonical_list(list(case.get("axioms_on", [])))
        base_pkg_key = _canonical_key(base_axioms_on)

        # enumerate all inclusion-minimal repairs from the atlas
        repairs_obj = _enumerate_case_repairs(
            case=case, case_by_mask=case_by_mask, axiom_universe=axiom_universe
        )
        # validate consistency against atlas statuses
        _validate_repairs(
            unsat_mask=unsat_mask,
            repairs=repairs_obj["mcs_all"],
            case_by_mask=case_by_mask,
            width=width,
        )

        all_repairs = repairs_obj["mcs_all"]
        repaired_keys: list[str] = []

        for repair in all_repairs:
            mcs_axioms = _canonical_list(list(repair["remove_axioms"]))
            mcs_key = _canonical_key(mcs_axioms)

            # A \ R_i
            mcs_set = set(mcs_axioms)
            repaired_axioms = _canonical_list([ax for ax in base_axioms_on if ax not in mcs_set])
            repaired_key = _canonical_key(repaired_axioms)

            # no duplicates
            dedup_key = (base_pkg_key, mcs_key)
            if dedup_key in seen_keys:
                raise RuntimeError(
                    f"Duplicate triple detected: base={base_pkg_key}, mcs={mcs_key}"
                )
            seen_keys.add(dedup_key)

            # cross-validate repaired_package is SAT in atlas
            remove_mask = int(repair["remove_mask_int"])
            repaired_mask = unsat_mask & ~remove_mask
            repaired_case = case_by_mask[repaired_mask]
            repaired_status = str(repaired_case.get("status", "UNKNOWN"))
            if repaired_status != "SAT":
                raise RuntimeError(
                    f"Repaired package {repaired_key} (mask={repaired_mask}) "
                    f"has status={repaired_status}, expected SAT. "
                    "Atlas may be inconsistent."
                )

            repaired_keys.append(repaired_key)

            triples.append({
                "case": "n2_m4",
                "axiom_family": CANONICAL_FAMILY,
                "base_package": base_axioms_on,
                "base_package_key": base_pkg_key,
                "base_mcs": mcs_axioms,
                "base_mcs_key": mcs_key,
                "repaired_package": repaired_axioms,
                "repaired_package_key": repaired_key,
                "source_unsat_artifact": str(
                    Path("results/jar_full_atlas") / case_id / "summary.json"
                ),
                "source_mcs_artifact": str(
                    Path("results/jar_full_atlas") / "atlas.json"
                    ) + " (enumerate_repairs full enumeration)",
                "validation": {
                    "base_package_status": "UNSAT",
                    "base_package_status_source": "atlas",
                    "repaired_package_status": "SAT",
                    "repaired_package_status_source": "atlas",
                    "mcs_minimality_verified": bool(repair.get("minimality_verified", False)),
                },
                "notes": SCOPE_NOTE,
            })

        per_package.append({
            "base_package_key": base_pkg_key,
            "base_package": base_axioms_on,
            "atlas_case_id": case_id,
            "n_repairs": len(all_repairs),
            "repaired_package_keys": repaired_keys,
        })

    # final duplicate check across all triples
    all_pair_keys = [(t["base_package_key"], t["base_mcs_key"]) for t in triples]
    if len(all_pair_keys) != len(set(all_pair_keys)):
        raise RuntimeError("Duplicate (base_package_key, base_mcs_key) pairs in output.")

    artifact = {
        "schema_version": "1",
        "generated_at_utc": datetime.now(timezone.utc).isoformat(),
        "date": date_str,
        "experiment": "repair_liftability_step1",
        "step": "Step 1: Fix all base-case repair triples",
        "case": "n2_m4",
        "n_voters": 2,
        "n_alternatives": 4,
        "axiom_family": CANONICAL_FAMILY,
        "scope_note": SCOPE_NOTE,
        "source_atlas": str(atlas_path.relative_to(REPO_ROOT)),
        "summary": {
            "n_unsat_base_packages": len(unsat_cases),
            "n_total_repairs": sum(p["n_repairs"] for p in per_package),
            "n_emitted_triples": len(triples),
            "per_package": per_package,
        },
        "triples": triples,
    }
    return artifact


# ── markdown summary ──────────────────────────────────────────────────────────

def build_markdown(artifact: dict[str, Any]) -> str:
    s = artifact["summary"]
    lines: list[str] = [
        "# Step 1: Base-Case Repair Triples",
        "",
        f"**Generated:** {artifact['generated_at_utc']}  ",
        f"**Base case:** n={artifact['n_voters']}, m={artifact['n_alternatives']} (`{artifact['case']}`)  ",
        f"**Axiom family:** {', '.join(artifact['axiom_family'])}  ",
        "",
        "## Scope note",
        "",
        artifact["scope_note"],
        "",
        "## Summary",
        "",
        f"| Item | Count |",
        f"|------|-------|",
        f"| UNSAT base packages | {s['n_unsat_base_packages']} |",
        f"| Total minimal repairs | {s['n_total_repairs']} |",
        f"| Emitted triples | {s['n_emitted_triples']} |",
        "",
        "## Per-package detail",
        "",
    ]

    for p in s["per_package"]:
        lines += [
            f"### `{p['base_package_key']}`",
            "",
            f"- Atlas case: `{p['atlas_case_id']}`",
            f"- Active levers: {p['base_package']}",
            f"- Number of minimal repairs: {p['n_repairs']}",
            f"- Repaired packages (A \\ R_i):",
            "",
        ]
        for rk in p["repaired_package_keys"]:
            lines.append(f"  - `{rk}`")
        lines.append("")

    lines += [
        "## Triple listing",
        "",
        "| # | Base package | MCS R_i | Repaired A\\\\R_i |",
        "|---|-------------|---------|----------------|",
    ]
    for i, t in enumerate(artifact["triples"], 1):
        lines.append(
            f"| {i} | `{t['base_package_key']}` | `{t['base_mcs_key']}` | `{t['repaired_package_key']}` |"
        )
    lines += [
        "",
        "## Interpretation scope",
        "",
        "All triples in this file are valid base inputs for Step 2 (liftability checks) "
        "under the restricted local-rationality interpretation of `no_cycle3` and `no_cycle4`.",
        "Do **not** interpret results from these triples as evidence about full `SocialAcyclic` "
        "unless a stronger rationality encoding is added in later work.",
        "",
        "See `docs/no_cycle_interpretation_note.md` and `docs/axiom_semantics_scaling.md`.",
        "",
    ]
    return "\n".join(lines)


# ── main ──────────────────────────────────────────────────────────────────────

def main() -> None:
    ap = argparse.ArgumentParser(
        description=(
            "Build Step 1 base-case repair triples for the repair-liftability experiment. "
            "Reads the solved base-case atlas, enumerates all inclusion-minimal repairs "
            "for each UNSAT axiom package, and writes base_triples.json + base_triples.md."
        )
    )
    ap.add_argument(
        "--atlas",
        type=Path,
        default=DEFAULT_ATLAS,
        help=f"Path to base-case atlas.json (default: {DEFAULT_ATLAS})",
    )
    ap.add_argument(
        "--date",
        type=str,
        default=None,
        help="Date label for the output directory, e.g. 20260401. "
             "If omitted, today's date (UTC) is used.",
    )
    ap.add_argument(
        "--outdir",
        type=Path,
        default=None,
        help="Output directory. If omitted, defaults to "
             "results/<date>/repair_liftability/ under the repo root.",
    )
    args = ap.parse_args()

    date_str = args.date or datetime.now(timezone.utc).strftime("%Y%m%d")

    outdir: Path
    if args.outdir is not None:
        outdir = args.outdir
    else:
        outdir = REPO_ROOT / "results" / date_str / "repair_liftability"

    atlas_path: Path = args.atlas
    if not atlas_path.exists():
        raise FileNotFoundError(f"atlas not found: {atlas_path}")

    print(f"Atlas:  {atlas_path}")
    print(f"Outdir: {outdir}")

    artifact = build_triples(atlas_path=atlas_path, date_str=date_str)

    outdir.mkdir(parents=True, exist_ok=True)
    triples_path = outdir / "base_triples.json"
    md_path = outdir / "base_triples.md"

    _write_json(triples_path, artifact)
    md_path.write_text(build_markdown(artifact), encoding="utf-8")

    s = artifact["summary"]
    print(f"\nStep 1 complete.")
    print(f"  UNSAT base packages : {s['n_unsat_base_packages']}")
    print(f"  Minimal repairs     : {s['n_total_repairs']}")
    print(f"  Emitted triples     : {s['n_emitted_triples']}")
    print(f"\nArtifacts written:")
    print(f"  {triples_path}")
    print(f"  {md_path}")


if __name__ == "__main__":
    main()
