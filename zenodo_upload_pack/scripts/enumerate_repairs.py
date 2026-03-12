#!/usr/bin/env python3
from __future__ import annotations

import argparse
import itertools
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any


def _load_json(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


def _write_json(path: Path, payload: dict[str, Any]) -> None:
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def _normalize_cases(atlas: dict[str, Any]) -> list[dict[str, Any]]:
    raw = atlas.get("cases", [])
    if isinstance(raw, list):
        return [c for c in raw if isinstance(c, dict)]
    if isinstance(raw, dict):
        return [c for c in raw.values() if isinstance(c, dict)]
    raise ValueError("atlas.cases must be a list or object")


def _mask_to_bits(mask: int, width: int) -> str:
    return "".join("1" if ((mask >> i) & 1) else "0" for i in range(width))


def _case_id(mask: int, width: int) -> str:
    return f"case_{_mask_to_bits(mask, width)}"


def _status(case: dict[str, Any]) -> str:
    return str(case.get("status", "UNKNOWN"))


def _case_lookup(cases: list[dict[str, Any]]) -> dict[int, dict[str, Any]]:
    mapping: dict[int, dict[str, Any]] = {}
    for case in cases:
        try:
            mask = int(case["mask_int"])
        except Exception as ex:
            raise ValueError(f"case missing integer mask_int: {case.get('case_id')}") from ex
        if mask in mapping:
            raise ValueError(f"duplicate mask_int in atlas cases: {mask}")
        mapping[mask] = case
    return mapping


def _validate_subcase(case: dict[str, Any], *, expected_case_id: str) -> None:
    if not bool(case.get("solved", False)):
        raise RuntimeError(
            f"case {expected_case_id} is required for repair enumeration but solved=false; "
            "re-run run_atlas.py with --prune none"
        )
    st = _status(case)
    if st not in {"SAT", "UNSAT"}:
        raise RuntimeError(
            f"case {expected_case_id} has non-decisive status '{st}'; "
            "repair enumeration requires solved SAT/UNSAT statuses"
        )


def _minimality_holds(
    *,
    unsat_mask: int,
    remove_indices: tuple[int, ...],
    case_by_mask: dict[int, dict[str, Any]],
    width: int,
) -> bool:
    for r in range(len(remove_indices)):
        for subset in itertools.combinations(remove_indices, r):
            subset_mask = 0
            for idx in subset:
                subset_mask |= 1 << idx
            sub_mask = unsat_mask & ~subset_mask
            sub_case = case_by_mask[sub_mask]
            if _status(sub_case) != "UNSAT":
                return False
    return True


def _enumerate_case_repairs(
    *,
    case: dict[str, Any],
    case_by_mask: dict[int, dict[str, Any]],
    axiom_universe: list[str],
) -> dict[str, Any]:
    width = len(axiom_universe)
    unsat_mask = int(case["mask_int"])
    on_indices = [i for i in range(width) if (unsat_mask >> i) & 1]
    repairs: list[dict[str, Any]] = []

    for size in range(1, len(on_indices) + 1):
        for remove_indices in itertools.combinations(on_indices, size):
            remove_mask = 0
            for idx in remove_indices:
                remove_mask |= 1 << idx
            sat_mask = unsat_mask & ~remove_mask
            sat_case = case_by_mask.get(sat_mask)
            expected_cid = _case_id(sat_mask, width)
            if sat_case is None:
                raise RuntimeError(
                    f"required subcase {expected_cid} missing while enumerating repairs for {case.get('case_id')}"
                )
            _validate_subcase(sat_case, expected_case_id=expected_cid)

            if _status(sat_case) != "SAT":
                continue
            if not _minimality_holds(
                unsat_mask=unsat_mask,
                remove_indices=remove_indices,
                case_by_mask=case_by_mask,
                width=width,
            ):
                continue

            remove_axioms = [axiom_universe[i] for i in remove_indices]
            repairs.append(
                {
                    "remove_mask_int": remove_mask,
                    "remove_bits": _mask_to_bits(remove_mask, width),
                    "remove_axioms": remove_axioms,
                    "size": len(remove_axioms),
                    "sat_case_mask_int": sat_mask,
                    "sat_case_bits": _mask_to_bits(sat_mask, width),
                    "sat_case_id": _case_id(sat_mask, width),
                    "sat_case_status": "SAT",
                    "minimality_verified": True,
                }
            )

    repairs = sorted(repairs, key=lambda x: (int(x["size"]), str(x["remove_bits"]), str(x["sat_case_id"])))
    if not repairs:
        raise RuntimeError(
            f"no axiom-level MCS found for UNSAT case {case.get('case_id')}; "
            "this indicates inconsistent atlas statuses or missing SAT neighbors"
        )

    min_size = int(repairs[0]["size"])
    min_repairs = [r for r in repairs if int(r["size"]) == min_size]
    return {
        "mcs_all": repairs,
        "mcs_min_size": min_size,
        "mcs_min_all": min_repairs,
    }


def _validate_repairs(
    *,
    unsat_mask: int,
    repairs: list[dict[str, Any]],
    case_by_mask: dict[int, dict[str, Any]],
    width: int,
) -> None:
    for repair in repairs:
        remove_mask = int(repair["remove_mask_int"])
        sat_mask = unsat_mask & ~remove_mask
        sat_case = case_by_mask[sat_mask]
        if _status(sat_case) != "SAT":
            raise RuntimeError(
                f"invalid repair {repair.get('remove_bits')}: resulting case {_case_id(sat_mask, width)} is not SAT"
            )
        remove_indices = tuple(i for i in range(width) if (remove_mask >> i) & 1)
        if not _minimality_holds(
            unsat_mask=unsat_mask,
            remove_indices=remove_indices,
            case_by_mask=case_by_mask,
            width=width,
        ):
            raise RuntimeError(f"invalid repair {repair.get('remove_bits')}: minimality check failed")


def main() -> None:
    ap = argparse.ArgumentParser(
        description="Enumerate all axiom-level inclusion-minimal repairs (MCS) for solved UNSAT atlas cases"
    )
    ap.add_argument("--outdir", type=Path, default=None, help="Atlas output directory containing atlas.json")
    ap.add_argument("--atlas", type=Path, default=None, help="Path to atlas.json (alternative to --outdir)")
    ap.add_argument("--atlas-out", type=Path, default=None, help="Output atlas path (default: overwrite input atlas)")
    args = ap.parse_args()

    if args.outdir is None and args.atlas is None:
        raise ValueError("one of --outdir or --atlas is required")

    atlas_path = args.atlas if args.atlas is not None else args.outdir / "atlas.json"
    if not atlas_path.exists():
        raise FileNotFoundError(f"missing atlas.json: {atlas_path}")

    outdir = args.outdir if args.outdir is not None else atlas_path.parent
    atlas = _load_json(atlas_path)
    cases = _normalize_cases(atlas)
    if int(atlas.get("cases_total", len(cases))) != len(cases):
        raise ValueError("atlas.cases_total does not match number of cases")

    axiom_universe = list(atlas.get("axiom_universe", []))
    width = len(axiom_universe)
    if width == 0:
        raise ValueError("atlas.axiom_universe must not be empty")

    case_by_mask = _case_lookup(cases)
    unsat_cases = [c for c in cases if _status(c) == "UNSAT"]
    if not unsat_cases:
        raise RuntimeError("no UNSAT cases in atlas.json")
    for c in unsat_cases:
        if not bool(c.get("solved", False)):
            raise RuntimeError(
                f"UNSAT case {c.get('case_id')} has solved=false; run full solve with --prune none before repair enumeration"
            )

    processed = 0
    for case in sorted(unsat_cases, key=lambda c: str(c.get("case_id", ""))):
        repairs_obj = _enumerate_case_repairs(case=case, case_by_mask=case_by_mask, axiom_universe=axiom_universe)
        _validate_repairs(
            unsat_mask=int(case["mask_int"]),
            repairs=repairs_obj["mcs_all"],
            case_by_mask=case_by_mask,
            width=width,
        )

        case["mcs_all"] = repairs_obj["mcs_all"]
        case["mcs_min_size"] = repairs_obj["mcs_min_size"]
        case["mcs_min_all"] = repairs_obj["mcs_min_all"]
        case["mcs_enumeration"] = {
            "status": "ok",
            "method": "axiom_level_full_enumeration_v1",
            "validated": True,
            "mcs_all_count": len(repairs_obj["mcs_all"]),
            "mcs_min_count": len(repairs_obj["mcs_min_all"]),
        }

        case_dir = outdir / str(case["case_id"])
        if case_dir.exists():
            payload = {
                "case_id": case["case_id"],
                "mask_int": case["mask_int"],
                "axioms_on": case.get("axioms_on", []),
                "mcs_all": repairs_obj["mcs_all"],
                "mcs_min_size": repairs_obj["mcs_min_size"],
                "mcs_min_all": repairs_obj["mcs_min_all"],
            }
            _write_json(case_dir / "mcs_all.json", payload)
            summary_path = case_dir / "summary.json"
            if summary_path.exists():
                summary_obj = _load_json(summary_path)
                summary_obj["mcs_all"] = repairs_obj["mcs_all"]
                summary_obj["mcs_min_size"] = repairs_obj["mcs_min_size"]
                summary_obj["mcs_min_all"] = repairs_obj["mcs_min_all"]
                _write_json(summary_path, summary_obj)
        processed += 1

    atlas["repair_enumeration"] = {
        "generated_at_utc": datetime.now(timezone.utc).isoformat(),
        "method": "axiom_level_full_enumeration_v1",
        "processed_unsat_cases": processed,
    }

    output_atlas = args.atlas_out if args.atlas_out is not None else atlas_path
    _write_json(output_atlas, atlas)
    print(f"Wrote {output_atlas}")


if __name__ == "__main__":
    main()
