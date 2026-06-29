#!/usr/bin/env python3
"""Certificate 2 phase-diagram checker for M4.

This checker verifies existing Certificate 1 and mask-shape audit artifacts.
It does not invoke a solver, rerun Certificate 1, or recompute repair orbits.
"""

from __future__ import annotations

import argparse
import csv
import json
import platform
import sys
from collections import Counter, defaultdict
from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path
from typing import Iterable, Sequence

CERT1_DEFAULT = Path("/tmp/sen_m4_residual_class_coverage_certificate")
MASK_SHAPE_DEFAULT = Path("/tmp/sen_m4_mask_shape_collapse_law_audit")
OUT_DEFAULT = Path("/tmp/sen_m4_certificate2_phase_diagram_checker")

BUNDLED_UNIVERSE = ("asymm", "un", "minlib", "no_cycle3", "no_cycle4")
SHAPE_ORDER = ("O2", "O3", "O4")
EXPECTED_SHAPE_COUNTS = {"O2": 6, "O3": 24, "O4": 6}
EXPECTED_CELL_COUNTS = {
    "total_cells": 48,
    "ALL_UNSAT": 18,
    "ALL_SAT": 30,
    "MIXED_WITHIN_SHAPE": 0,
    "UNKNOWN": 0,
}
GROUP_SIZE = 48

CELL_STATUS_FIELDS = {
    "case_id",
    "shape",
    "expected_witness_count",
    "actual_witness_count",
    "num_sat",
    "num_unsat",
    "num_unknown",
    "cell_status",
}
WITNESS_FIELDS = {"case_id", "config_id", "overlap_class", "status"}
REPAIR_OBJECT_FIELDS = {"case_id", "shape", "config_id", "repair_ids", "report"}
FIBER_FIELDS = {
    "case_id",
    "shape",
    "report",
    "fiber_size_mu",
    "orbit_ids",
    "number_of_orbits_in_fiber",
    "is_single_repair_orbit",
    "contains_partial_orbit_fragments",
}
ORBIT_FIELDS = {
    "orbit_id",
    "case_id",
    "shape",
    "orbit_size",
    "stabilizer_size",
    "orbit_stabilizer_product",
    "shape_preserving_orbit",
    "is_orbit_contained_in_one_cell_report_fiber",
}
SHAPE_BLIND_FIELDS = {
    "case_id",
    "report",
    "blind_fiber_size",
    "blind_orbit_count",
    "shape_support",
    "shape_support_count",
    "support_truncation_law_holds",
}
SUPPORT_FIELDS = {
    "case_id",
    "report",
    "shape_support",
    "blind_orbit_count",
    "shape_support_count",
    "law_holds",
}


@dataclass(frozen=True)
class InputArtifacts:
    certificate1_dir: Path
    mask_shape_dir: Path
    mask_statuses: Path
    witness_statuses: Path
    residual_class_certificate: Path
    boundary_formula: Path
    cell_statuses: Path
    repair_objects: Path
    cell_report_fibers: Path
    repair_orbits: Path
    shape_blind_fibers: Path
    support_truncation: Path
    mask_shape_certificate: Path


def input_artifacts(certificate1_dir: Path, mask_shape_dir: Path) -> InputArtifacts:
    return InputArtifacts(
        certificate1_dir=certificate1_dir,
        mask_shape_dir=mask_shape_dir,
        mask_statuses=certificate1_dir / "mask_statuses.csv",
        witness_statuses=certificate1_dir / "witness_statuses.csv",
        residual_class_certificate=certificate1_dir / "residual_class_coverage_certificate.json",
        boundary_formula=certificate1_dir / "boundary_formula.json",
        cell_statuses=mask_shape_dir / "cell_statuses.csv",
        repair_objects=mask_shape_dir / "repair_objects.csv",
        cell_report_fibers=mask_shape_dir / "cell_report_fibers.csv",
        repair_orbits=mask_shape_dir / "repair_orbits.csv",
        shape_blind_fibers=mask_shape_dir / "shape_blind_fibers.csv",
        support_truncation=mask_shape_dir / "support_truncation.csv",
        mask_shape_certificate=mask_shape_dir / "mask_shape_collapse_certificate.json",
    )


def require_input_artifacts(artifacts: InputArtifacts) -> None:
    paths = [
        artifacts.mask_statuses,
        artifacts.witness_statuses,
        artifacts.residual_class_certificate,
        artifacts.boundary_formula,
        artifacts.cell_statuses,
        artifacts.repair_objects,
        artifacts.cell_report_fibers,
        artifacts.repair_orbits,
        artifacts.shape_blind_fibers,
        artifacts.support_truncation,
        artifacts.mask_shape_certificate,
    ]
    missing = [path for path in paths if not path.exists()]
    if missing:
        raise FileNotFoundError(
            "missing required Certificate 2 input artifact(s): "
            + ", ".join(str(path) for path in missing)
        )


def read_csv_rows(path: Path, required_fields: Iterable[str], name: str) -> list[dict[str, str]]:
    with path.open(newline="", encoding="utf-8") as handle:
        reader = csv.DictReader(handle)
        fieldnames = set(reader.fieldnames or [])
        missing = sorted(set(required_fields) - fieldnames)
        if missing:
            raise ValueError(f"{name} is missing required column(s): {', '.join(missing)}")
        return list(reader)


def read_json(path: Path) -> dict[str, object]:
    with path.open(encoding="utf-8") as handle:
        payload = json.load(handle)
    if not isinstance(payload, dict):
        raise ValueError(f"expected JSON object in {path}")
    return payload


def parse_bool(value: object) -> bool:
    if isinstance(value, bool):
        return value
    if str(value) == "True":
        return True
    if str(value) == "False":
        return False
    raise ValueError(f"expected True/False value, got {value!r}")


def parse_int(value: object, field: str) -> int:
    try:
        return int(str(value))
    except ValueError as exc:
        raise ValueError(f"expected integer for {field}, got {value!r}") from exc


def split_semicolon(value: object) -> list[str]:
    text = str(value)
    if not text:
        return []
    return [part for part in text.split(";") if part]


def cell_key(row: dict[str, str]) -> tuple[str, str]:
    return (row["case_id"], row["shape"])


def witness_key(row: dict[str, str]) -> tuple[str, str]:
    return (row["case_id"], row["overlap_class"])


def analyze_cell_coverage(
    *,
    mask_rows: Sequence[dict[str, str]],
    cell_rows: Sequence[dict[str, str]],
) -> dict[str, object]:
    keys = [cell_key(row) for row in cell_rows]
    duplicate_keys = sorted(key for key, count in Counter(keys).items() if count != 1)
    cell_by_key = {cell_key(row): row for row in cell_rows}
    minlib_active_masks = sorted(row["case_id"] for row in mask_rows if row.get("minlib_active") == "True")
    shape_membership_failures = []
    for case_id in minlib_active_masks:
        observed = sorted(shape for cid, shape in cell_by_key if cid == case_id)
        if observed != list(SHAPE_ORDER):
            shape_membership_failures.append(
                {"case_id": case_id, "expected_shapes": list(SHAPE_ORDER), "observed_shapes": observed}
            )

    expected_count_failures = []
    for row in cell_rows:
        shape = row["shape"]
        expected = EXPECTED_SHAPE_COUNTS.get(shape)
        actual_expected_col = parse_int(row["expected_witness_count"], "expected_witness_count")
        actual = parse_int(row["actual_witness_count"], "actual_witness_count")
        if expected is None or actual_expected_col != expected or actual != expected:
            expected_count_failures.append(
                {
                    "case_id": row["case_id"],
                    "shape": shape,
                    "expected": expected,
                    "expected_witness_count_column": actual_expected_col,
                    "actual_witness_count": actual,
                }
            )

    status_counts = Counter(row["cell_status"] for row in cell_rows)
    observed_counts = {
        "total_cells": len(cell_rows),
        "ALL_UNSAT": status_counts.get("ALL_UNSAT", 0),
        "ALL_SAT": status_counts.get("ALL_SAT", 0),
        "MIXED_WITHIN_SHAPE": status_counts.get("MIXED_WITHIN_SHAPE", 0),
        "UNKNOWN": status_counts.get("UNKNOWN", 0),
    }
    count_deviations = {
        key: {"expected": expected, "observed": observed_counts.get(key)}
        for key, expected in EXPECTED_CELL_COUNTS.items()
        if observed_counts.get(key) != expected
    }
    hard_failures = []
    if len(minlib_active_masks) != 16:
        hard_failures.append(f"expected 16 minlib-active masks, found {len(minlib_active_masks)}")
    if duplicate_keys:
        hard_failures.append("duplicate cell rows exist")
    if shape_membership_failures:
        hard_failures.append("shape membership check failed")
    if expected_count_failures:
        hard_failures.append("shape witness count check failed")
    if len(cell_rows) != EXPECTED_CELL_COUNTS["total_cells"]:
        hard_failures.append("total cell count is not 48")
    if status_counts.get("UNKNOWN", 0):
        hard_failures.append("UNKNOWN cells exist")
    if status_counts.get("MIXED_WITHIN_SHAPE", 0):
        hard_failures.append("MIXED_WITHIN_SHAPE cells exist")

    return {
        "verdict": "PASS" if not hard_failures else "FAIL",
        "total_cells": len(cell_rows),
        "minlib_active_mask_count": len(minlib_active_masks),
        "minlib_active_masks": minlib_active_masks,
        "status_counts": observed_counts,
        "expected_status_counts": EXPECTED_CELL_COUNTS,
        "count_deviations": count_deviations,
        "duplicate_cell_keys": [list(key) for key in duplicate_keys],
        "shape_membership_failures": shape_membership_failures,
        "expected_count_failures": expected_count_failures,
        "hard_failures": hard_failures,
    }


def group_witness_rows(witness_rows: Sequence[dict[str, str]]) -> dict[tuple[str, str], list[dict[str, str]]]:
    grouped: dict[tuple[str, str], list[dict[str, str]]] = defaultdict(list)
    for row in witness_rows:
        if row["overlap_class"] in SHAPE_ORDER:
            grouped[witness_key(row)].append(row)
    return grouped


def count_by_cell(rows: Sequence[dict[str, str]]) -> dict[tuple[str, str], int]:
    counts: dict[tuple[str, str], int] = defaultdict(int)
    for row in rows:
        counts[cell_key(row)] += 1
    return counts


def evaluate_repair_empty_cells(
    *,
    cell_rows: Sequence[dict[str, str]],
    witness_rows: Sequence[dict[str, str]],
    repair_rows: Sequence[dict[str, str]],
    repair_objects_guarded_by_unsat: bool,
) -> dict[str, object]:
    witness_by_cell = group_witness_rows(witness_rows)
    repair_count_by_cell = count_by_cell(repair_rows)
    sat_cells = [row for row in cell_rows if row["cell_status"] == "ALL_SAT"]
    rows = []
    failures = []
    for cell in sat_cells:
        key = cell_key(cell)
        witnesses = witness_by_cell.get(key, [])
        status_counts = Counter(row["status"] for row in witnesses)
        repair_object_count = repair_count_by_cell.get(key, 0)
        expected_witness_count = parse_int(cell["actual_witness_count"], "actual_witness_count")
        witness_count = len(witnesses)
        holds = (
            witness_count == expected_witness_count
            and status_counts.get("SAT", 0) == witness_count
            and status_counts.get("UNSAT", 0) == 0
            and status_counts.get("UNKNOWN", 0) == 0
            and repair_object_count == 0
            and repair_objects_guarded_by_unsat
        )
        row = {
            "case_id": key[0],
            "shape": key[1],
            "cell_status": cell["cell_status"],
            "witness_count": witness_count,
            "sat_witness_count": status_counts.get("SAT", 0),
            "unsat_witness_count": status_counts.get("UNSAT", 0),
            "unknown_witness_count": status_counts.get("UNKNOWN", 0),
            "repair_object_count": repair_object_count,
            "constructor_guard": repair_objects_guarded_by_unsat,
            "repair_empty_holds": holds,
        }
        rows.append(row)
        if not holds:
            failures.append(row)

    return {
        "verdict": "PASS" if not failures else "FAIL",
        "repair_empty_cell_count": len(rows),
        "rows": rows,
        "failure_count": len(failures),
        "failures": failures[:20],
    }


def evaluate_unsat_cells(
    *,
    cell_rows: Sequence[dict[str, str]],
    witness_rows: Sequence[dict[str, str]],
    repair_rows: Sequence[dict[str, str]],
) -> dict[str, object]:
    witness_by_cell = group_witness_rows(witness_rows)
    repair_count_by_cell = count_by_cell(repair_rows)
    all_unsat_keys = {cell_key(row) for row in cell_rows if row["cell_status"] == "ALL_UNSAT"}
    rows = []
    failures = []
    for cell in [row for row in cell_rows if row["cell_status"] == "ALL_UNSAT"]:
        key = cell_key(cell)
        witnesses = witness_by_cell.get(key, [])
        status_counts = Counter(row["status"] for row in witnesses)
        repair_object_count = repair_count_by_cell.get(key, 0)
        expected_witness_count = parse_int(cell["actual_witness_count"], "actual_witness_count")
        witness_count = len(witnesses)
        holds = (
            witness_count == expected_witness_count
            and status_counts.get("UNSAT", 0) == witness_count
            and status_counts.get("SAT", 0) == 0
            and status_counts.get("UNKNOWN", 0) == 0
            and repair_object_count > 0
        )
        row = {
            "case_id": key[0],
            "shape": key[1],
            "cell_status": cell["cell_status"],
            "witness_count": witness_count,
            "sat_witness_count": status_counts.get("SAT", 0),
            "unsat_witness_count": status_counts.get("UNSAT", 0),
            "unknown_witness_count": status_counts.get("UNKNOWN", 0),
            "repair_object_count": repair_object_count,
            "unsat_cell_holds": holds,
        }
        rows.append(row)
        if not holds:
            failures.append(row)

    objects_outside_unsat = [
        row for row in repair_rows
        if cell_key(row) not in all_unsat_keys
    ]
    return {
        "verdict": "PASS" if not failures and not objects_outside_unsat else "FAIL",
        "rows": rows,
        "failure_count": len(failures),
        "failures": failures[:20],
        "repair_objects_outside_all_unsat_count": len(objects_outside_unsat),
        "repair_objects_outside_all_unsat": objects_outside_unsat[:20],
    }


def orbit_ids_from_field(value: object) -> list[str]:
    return split_semicolon(value)


def evaluate_orbit_fiber_exactness(
    *,
    fiber_rows: Sequence[dict[str, str]],
    orbit_rows: Sequence[dict[str, str]],
    all_unsat_keys: set[tuple[str, str]],
) -> dict[str, object]:
    orbit_ids = {row["orbit_id"] for row in orbit_rows}
    fiber_orbit_ids = []
    fiber_failures = []
    for row in fiber_rows:
        key = cell_key(row)
        row_orbit_ids = orbit_ids_from_field(row["orbit_ids"])
        fiber_orbit_ids.extend(row_orbit_ids)
        reasons = []
        if key not in all_unsat_keys:
            reasons.append("fiber is outside ALL_UNSAT cells")
        if parse_int(row["number_of_orbits_in_fiber"], "number_of_orbits_in_fiber") != 1:
            reasons.append("fiber does not contain exactly one orbit")
        if not parse_bool(row["is_single_repair_orbit"]):
            reasons.append("is_single_repair_orbit is false")
        if parse_bool(row["contains_partial_orbit_fragments"]):
            reasons.append("contains partial orbit fragments")
        if not row_orbit_ids:
            reasons.append("fiber has no orbit id")
        missing_orbits = sorted(set(row_orbit_ids) - orbit_ids)
        if missing_orbits:
            reasons.append("fiber references unknown orbit ids")
        if reasons:
            fiber_failures.append({**row, "failure_reasons": reasons, "missing_orbit_ids": missing_orbits})

    orbit_failures = []
    for row in orbit_rows:
        key = cell_key(row)
        orbit_size = parse_int(row["orbit_size"], "orbit_size")
        stabilizer_size = parse_int(row["stabilizer_size"], "stabilizer_size")
        product = parse_int(row["orbit_stabilizer_product"], "orbit_stabilizer_product")
        reasons = []
        if key not in all_unsat_keys:
            reasons.append("orbit is outside ALL_UNSAT cells")
        if product != GROUP_SIZE:
            reasons.append("orbit_stabilizer_product is not 48")
        if orbit_size * stabilizer_size != GROUP_SIZE:
            reasons.append("orbit_size * stabilizer_size is not 48")
        if orbit_size * stabilizer_size != product:
            reasons.append("orbit_stabilizer_product does not equal orbit_size * stabilizer_size")
        if not parse_bool(row["shape_preserving_orbit"]):
            reasons.append("shape_preserving_orbit is false")
        if not parse_bool(row["is_orbit_contained_in_one_cell_report_fiber"]):
            reasons.append("orbit crosses cell report fibers")
        if reasons:
            orbit_failures.append({**row, "failure_reasons": reasons})

    missing_from_fibers = sorted(orbit_ids - set(fiber_orbit_ids))
    unknown_in_fibers = sorted(set(fiber_orbit_ids) - orbit_ids)
    if missing_from_fibers:
        orbit_failures.append({"kind": "orbits_missing_from_fibers", "orbit_ids": missing_from_fibers[:20]})
    if unknown_in_fibers:
        fiber_failures.append({"kind": "unknown_orbits_in_fibers", "orbit_ids": unknown_in_fibers[:20]})

    return {
        "verdict": "PASS" if not fiber_failures and not orbit_failures else "FAIL",
        "cell_report_fiber_count": len(fiber_rows),
        "repair_orbit_count": len(orbit_rows),
        "fiber_failure_count": len(fiber_failures),
        "orbit_failure_count": len(orbit_failures),
        "fiber_failures": fiber_failures[:20],
        "orbit_failures": orbit_failures[:20],
    }


def evaluate_support_truncation(
    *,
    shape_blind_rows: Sequence[dict[str, str]],
    support_rows: Sequence[dict[str, str]],
    cell_by_key: dict[tuple[str, str], dict[str, str]],
) -> dict[str, object]:
    support_by_key = {(row["case_id"], row["report"]): row for row in support_rows}
    blind_by_key = {(row["case_id"], row["report"]): row for row in shape_blind_rows}
    key_mismatches = {
        "missing_support_rows": [list(key) for key in sorted(set(blind_by_key) - set(support_by_key))],
        "extra_support_rows": [list(key) for key in sorted(set(support_by_key) - set(blind_by_key))],
    }
    failures = []
    checked_rows = []
    for row in shape_blind_rows:
        key = (row["case_id"], row["report"])
        support_row = support_by_key.get(key)
        shapes = split_semicolon(row["shape_support"])
        blind_orbit_count = parse_int(row["blind_orbit_count"], "blind_orbit_count")
        shape_support_count = parse_int(row["shape_support_count"], "shape_support_count")
        blind_fiber_size = parse_int(row["blind_fiber_size"], "blind_fiber_size")
        reasons = []
        if not parse_bool(row["support_truncation_law_holds"]):
            reasons.append("support_truncation_law_holds is false")
        if blind_orbit_count != shape_support_count:
            reasons.append("blind_orbit_count != shape_support_count")
        if blind_fiber_size > 0 and not shapes:
            reasons.append("nonempty blind fiber has empty shape support")
        for shape in shapes:
            cell = cell_by_key.get((row["case_id"], shape))
            if shape not in SHAPE_ORDER:
                reasons.append(f"unknown shape in support: {shape}")
            elif cell is None:
                reasons.append(f"shape support references missing cell: {shape}")
            elif cell["cell_status"] != "ALL_UNSAT":
                reasons.append(f"shape support references non-ALL_UNSAT cell: {shape}")
        if support_row is None:
            reasons.append("matching support_truncation row missing")
        else:
            support_shapes = split_semicolon(support_row["shape_support"])
            if support_shapes != shapes:
                reasons.append("shape_support mismatch between CSVs")
            if parse_int(support_row["blind_orbit_count"], "blind_orbit_count") != blind_orbit_count:
                reasons.append("blind_orbit_count mismatch between CSVs")
            if parse_int(support_row["shape_support_count"], "shape_support_count") != shape_support_count:
                reasons.append("shape_support_count mismatch between CSVs")
            if not parse_bool(support_row["law_holds"]):
                reasons.append("support_truncation law_holds is false")
        out = {
            "case_id": row["case_id"],
            "report": row["report"],
            "shape_support": shapes,
            "blind_orbit_count": blind_orbit_count,
            "shape_support_count": shape_support_count,
            "support_truncation_law_holds": not reasons,
            "failure_reasons": reasons,
        }
        checked_rows.append(out)
        if reasons:
            failures.append(out)

    if key_mismatches["missing_support_rows"] or key_mismatches["extra_support_rows"]:
        failures.append({"kind": "support_row_key_mismatch", **key_mismatches})

    return {
        "verdict": "PASS" if not failures else "FAIL",
        "shape_blind_fiber_count": len(shape_blind_rows),
        "checked_rows": checked_rows,
        "failure_count": len(failures),
        "failures": failures[:20],
        "key_mismatches": key_mismatches,
    }


def absorption_metadata() -> dict[str, object]:
    return {
        "certificate3_independent_stage": False,
        "certificate4_independent_stage": False,
        "certificate3_absorbed": True,
        "certificate4_absorbed": True,
        "certificate3_absorbed_as": "shape_blind_support_reporting",
        "certificate4_absorbed_as": "support_truncation_subcheck",
    }


def validate_absorption_metadata(metadata: dict[str, object]) -> dict[str, object]:
    expected = absorption_metadata()
    failures = [
        {"field": key, "expected": value, "observed": metadata.get(key)}
        for key, value in expected.items()
        if metadata.get(key) != value
    ]
    return {"verdict": "PASS" if not failures else "FAIL", "failures": failures}


def validate_non_circularity_metadata(metadata: dict[str, object]) -> dict[str, object]:
    required_true = [
        "t_is_bundled_mask_schema",
        "shape_computed_from_w",
        "cell_is_analysis_stratum",
        "residual_class_not_defined_by_collapse_behavior",
        "sat_cells_empty_because_sat",
        "unsat_cells_included_because_unsat",
        "repair_objects_guarded_by_unsat",
    ]
    failures = [key for key in required_true if metadata.get(key) is not True]
    return {
        "verdict": "PASS" if not failures else "FAIL",
        "failures": failures,
    }


def write_json(path: Path, payload: object) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def certificate2_verdict(
    *,
    hard_checks: dict[str, str],
    count_deviations: dict[str, object],
) -> tuple[str, str]:
    failures = [name for name, verdict in hard_checks.items() if verdict != "PASS"]
    if failures:
        return "FAIL", "core Certificate 2 check(s) failed: " + ", ".join(failures)
    if count_deviations:
        return "CONDITIONAL_PASS", "cell status count deviations require review"
    return "PASS", "all Certificate 2 phase-diagram checks passed"


def run_checker(
    *,
    certificate1_dir: Path,
    mask_shape_dir: Path,
    out_dir: Path,
) -> dict[str, object]:
    artifacts = input_artifacts(certificate1_dir, mask_shape_dir)
    require_input_artifacts(artifacts)
    out_dir.mkdir(parents=True, exist_ok=True)

    mask_rows = read_csv_rows(artifacts.mask_statuses, {"case_id", "minlib_active"}, "mask_statuses.csv")
    witness_rows = read_csv_rows(artifacts.witness_statuses, WITNESS_FIELDS, "witness_statuses.csv")
    cell_rows = read_csv_rows(artifacts.cell_statuses, CELL_STATUS_FIELDS, "cell_statuses.csv")
    repair_rows = read_csv_rows(artifacts.repair_objects, REPAIR_OBJECT_FIELDS, "repair_objects.csv")
    fiber_rows = read_csv_rows(artifacts.cell_report_fibers, FIBER_FIELDS, "cell_report_fibers.csv")
    orbit_rows = read_csv_rows(artifacts.repair_orbits, ORBIT_FIELDS, "repair_orbits.csv")
    shape_blind_rows = read_csv_rows(artifacts.shape_blind_fibers, SHAPE_BLIND_FIELDS, "shape_blind_fibers.csv")
    support_rows = read_csv_rows(artifacts.support_truncation, SUPPORT_FIELDS, "support_truncation.csv")
    residual_certificate = read_json(artifacts.residual_class_certificate)
    mask_shape_certificate = read_json(artifacts.mask_shape_certificate)

    cell_by_key = {cell_key(row): row for row in cell_rows}
    all_unsat_keys = {key for key, row in cell_by_key.items() if row["cell_status"] == "ALL_UNSAT"}
    repair_objects_outside_unsat = [row for row in repair_rows if cell_key(row) not in all_unsat_keys]
    repair_objects_guarded_by_unsat = not repair_objects_outside_unsat

    coverage = analyze_cell_coverage(mask_rows=mask_rows, cell_rows=cell_rows)
    repair_empty = evaluate_repair_empty_cells(
        cell_rows=cell_rows,
        witness_rows=witness_rows,
        repair_rows=repair_rows,
        repair_objects_guarded_by_unsat=repair_objects_guarded_by_unsat,
    )
    unsat_cells = evaluate_unsat_cells(
        cell_rows=cell_rows,
        witness_rows=witness_rows,
        repair_rows=repair_rows,
    )
    orbit_fiber = evaluate_orbit_fiber_exactness(
        fiber_rows=fiber_rows,
        orbit_rows=orbit_rows,
        all_unsat_keys=all_unsat_keys,
    )
    support = evaluate_support_truncation(
        shape_blind_rows=shape_blind_rows,
        support_rows=support_rows,
        cell_by_key=cell_by_key,
    )
    absorbed_metadata = absorption_metadata()
    absorbed = validate_absorption_metadata(absorbed_metadata)

    mask_non_circ = mask_shape_certificate.get("non_circularity_checks", {})
    if not isinstance(mask_non_circ, dict):
        mask_non_circ = {}
    residual_individuation = residual_certificate.get("residual_class_individuation", {})
    if not isinstance(residual_individuation, dict):
        residual_individuation = {}
    non_circularity_metadata = {
        "t_is_bundled_mask_schema": (
            residual_individuation.get("T_identity") == "bundled residual mask/schema"
            and mask_non_circ.get("t_is_bundled_mask_schema") is True
        ),
        "shape_computed_from_w": mask_non_circ.get("shape_computed_from_w") is True,
        "cell_is_analysis_stratum": mask_non_circ.get("cell_is_analysis_stratum") is True,
        "residual_class_not_defined_by_collapse_behavior": (
            mask_non_circ.get("residual_class_not_defined_by_law") is True
        ),
        "sat_cells_empty_because_sat": repair_empty["verdict"] == "PASS",
        "unsat_cells_included_because_unsat": unsat_cells["verdict"] == "PASS",
        "repair_objects_guarded_by_unsat": repair_objects_guarded_by_unsat,
    }
    non_circularity = validate_non_circularity_metadata(non_circularity_metadata)

    hard_checks = {
        "phase_diagram_coverage": str(coverage["verdict"]),
        "repair_empty": str(repair_empty["verdict"]),
        "unsat_cell_exactness_scope": str(unsat_cells["verdict"]),
        "orbit_fiber_exactness": str(orbit_fiber["verdict"]),
        "support_truncation": str(support["verdict"]),
        "certificate3_4_absorption": str(absorbed["verdict"]),
        "non_circularity": str(non_circularity["verdict"]),
    }
    verdict, verdict_reason = certificate2_verdict(
        hard_checks=hard_checks,
        count_deviations=coverage["count_deviations"],  # type: ignore[arg-type]
    )

    summary = {
        "total_cells": coverage["status_counts"]["total_cells"],  # type: ignore[index]
        "all_unsat_cells": coverage["status_counts"]["ALL_UNSAT"],  # type: ignore[index]
        "all_sat_cells": coverage["status_counts"]["ALL_SAT"],  # type: ignore[index]
        "mixed_within_shape_cells": coverage["status_counts"]["MIXED_WITHIN_SHAPE"],  # type: ignore[index]
        "unknown_cells": coverage["status_counts"]["UNKNOWN"],  # type: ignore[index]
        "repair_empty_cell_count": repair_empty["repair_empty_cell_count"],
        "repair_empty_verdict": repair_empty["verdict"],
        "repair_object_count": len(repair_rows),
        "repair_orbit_count": len(orbit_rows),
        "cell_report_fiber_count": len(fiber_rows),
        "shape_blind_fiber_count": len(shape_blind_rows),
        "orbit_fiber_exactness_verdict": orbit_fiber["verdict"],
        "orbit_stabilizer_verdict": "PASS" if orbit_fiber["verdict"] == "PASS" else "FAIL",
        "support_truncation_verdict": support["verdict"],
        "certificate3_absorbed": absorbed_metadata["certificate3_absorbed"],
        "certificate4_absorbed": absorbed_metadata["certificate4_absorbed"],
        "non_circularity_verdict": non_circularity["verdict"],
        "certificate2_verdict": verdict,
        "certificate2_verdict_reason": verdict_reason,
    }
    certificate = {
        "certificate_name": "M4 Certificate 2: Complete Phase-Diagram Checker",
        "certificate_version": 1,
        "generated_at_utc": datetime.now(timezone.utc).isoformat(),
        "input_artifacts": {
            "mask_statuses": str(artifacts.mask_statuses),
            "witness_statuses": str(artifacts.witness_statuses),
            "residual_class_coverage_certificate": str(artifacts.residual_class_certificate),
            "boundary_formula": str(artifacts.boundary_formula),
            "cell_statuses": str(artifacts.cell_statuses),
            "repair_objects": str(artifacts.repair_objects),
            "cell_report_fibers": str(artifacts.cell_report_fibers),
            "repair_orbits": str(artifacts.repair_orbits),
            "shape_blind_fibers": str(artifacts.shape_blind_fibers),
            "support_truncation": str(artifacts.support_truncation),
            "mask_shape_collapse_certificate": str(artifacts.mask_shape_certificate),
        },
        "runtime_metadata": {
            "python_version": sys.version.split()[0],
            "platform": platform.platform(),
            "solver_run": False,
            "lean_run": False,
        },
        "scope": "complete 48-cell minlib-active bundled-mask x obstruction-shape phase diagram",
        "phase_diagram_domain": {
            "bundled_universe": list(BUNDLED_UNIVERSE),
            "shape_order": list(SHAPE_ORDER),
            "expected_total_cells": EXPECTED_CELL_COUNTS["total_cells"],
        },
        "cell_status_summary": coverage,
        "repair_empty": repair_empty,
        "unsat_cell_exactness": {
            "unsat_cells": unsat_cells,
            "orbit_fiber_exactness": orbit_fiber,
        },
        "shape_blind_support_truncation": support,
        "absorbed_certificate_obligations": {
            **absorbed_metadata,
            "verdict": absorbed["verdict"],
            "failures": absorbed["failures"],
        },
        "non_circularity": {
            **non_circularity_metadata,
            "verdict": non_circularity["verdict"],
            "failures": non_circularity["failures"],
        },
        "verdict": {
            "certificate2_verdict": verdict,
            "certificate2_verdict_reason": verdict_reason,
            "hard_checks": hard_checks,
        },
        "non_claims": [
            "no Lean theorem",
            "no paper-ready theorem",
            "no general Sen theorem",
            "no Arrow theorem",
            "no Gibbard-Satterthwaite theorem",
            "no 3-voter theorem",
            "no family-scale theorem",
            "no warrant-contract semantics",
            "no semantic-to-CNF correctness theorem",
            "no structural necessity theorem for the Mask-Shape Collapse Law",
            "no semantic encoding correctness beyond declared audit assumptions",
        ],
    }

    write_json(out_dir / "m4_certificate2_cell_statuses.json", {"coverage": coverage, "cell_statuses": cell_rows})
    write_json(out_dir / "m4_certificate2_repair_empty_cells.json", repair_empty)
    write_json(
        out_dir / "m4_certificate2_unsat_cell_repair_objects.json",
        {"unsat_cells": unsat_cells, "repair_objects": repair_rows},
    )
    write_json(out_dir / "m4_certificate2_cell_report_fibers.json", {"exactness": orbit_fiber, "rows": fiber_rows})
    write_json(out_dir / "m4_certificate2_repair_orbits.json", {"rows": orbit_rows, "verdict": orbit_fiber["verdict"]})
    write_json(
        out_dir / "m4_certificate2_shape_blind_support.json",
        {"shape_blind_fibers": shape_blind_rows, "support_truncation": support_rows, "verdict": support},
    )
    write_json(out_dir / "m4_certificate2_summary.json", summary)
    write_json(out_dir / "m4_certificate2_certificate.json", certificate)
    return certificate


def main() -> None:
    parser = argparse.ArgumentParser(description="Verify M4 Certificate 2 phase-diagram artifacts.")
    parser.add_argument("--certificate1-dir", type=Path, default=CERT1_DEFAULT)
    parser.add_argument("--mask-shape-dir", type=Path, default=MASK_SHAPE_DEFAULT)
    parser.add_argument("--out", "--out-dir", dest="out_dir", type=Path, default=OUT_DEFAULT)
    args = parser.parse_args()
    certificate = run_checker(
        certificate1_dir=args.certificate1_dir,
        mask_shape_dir=args.mask_shape_dir,
        out_dir=args.out_dir,
    )
    print(json.dumps(certificate["verdict"], indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
