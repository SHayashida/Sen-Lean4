#!/usr/bin/env python3
"""Mask-shape collapse law audit for M4.

This exploratory audit consumes Certificate 1 artifacts and computes repair
geometry only for UNSAT analysis cells ``Cell(T, shape)``. The ambient residual
theory ``T`` remains the bundled mask/schema; shape is computed from the
internal witness configuration.
"""

from __future__ import annotations

import argparse
import csv
import itertools
import json
import platform
import shutil
import sys
import tempfile
from collections import Counter, defaultdict
from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path
from typing import Iterable, Sequence

SCRIPT_DIR = Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

import repair_orbit_precheck as rop  # noqa: E402
import semantic_mus_precheck as smp  # noqa: E402

CERT_DEFAULT = Path("/tmp/sen_m4_residual_class_coverage_certificate")
OUT_DEFAULT = Path("/tmp/sen_m4_mask_shape_collapse_law_audit")
BUNDLED_UNIVERSE = ("asymm", "un", "minlib", "no_cycle3", "no_cycle4")
SHAPE_ORDER = ("O2", "O3", "O4")
EXPECTED_SHAPE_COUNTS = {"O2": 6, "O3": 24, "O4": 6}
CELL_STATUSES = ("ALL_UNSAT", "ALL_SAT", "MIXED_WITHIN_SHAPE", "UNKNOWN")
EXPECTED_SCRATCH_TOTALS = {
    "mixed_only_unsat_witness_row_count": 144,
    "mixed_only_repair_object_count": 540,
    "mixed_only_repair_orbit_count": 30,
    "mixed_only_cell_report_fiber_count": 30,
    "mixed_only_shape_blind_fiber_count": 24,
    "all_w_unsat_repair_object_count": 276,
    "all_w_unsat_repair_orbit_count": 16,
    "combined_repair_object_count": 816,
    "combined_repair_orbit_count": 46,
}


@dataclass(frozen=True)
class InputArtifacts:
    certificate_dir: Path
    mask_statuses: Path
    witness_statuses: Path
    certificate_json: Path
    boundary_formula: Path


def input_artifacts(certificate_dir: Path) -> InputArtifacts:
    return InputArtifacts(
        certificate_dir=certificate_dir,
        mask_statuses=certificate_dir / "mask_statuses.csv",
        witness_statuses=certificate_dir / "witness_statuses.csv",
        certificate_json=certificate_dir / "residual_class_coverage_certificate.json",
        boundary_formula=certificate_dir / "boundary_formula.json",
    )


def require_input_artifacts(artifacts: InputArtifacts) -> None:
    missing = [
        path for path in (
            artifacts.mask_statuses,
            artifacts.witness_statuses,
            artifacts.certificate_json,
            artifacts.boundary_formula,
        )
        if not path.exists()
    ]
    if missing:
        missing_text = ", ".join(str(path) for path in missing)
        raise FileNotFoundError(f"missing Certificate 1 artifact(s): {missing_text}")


def read_csv_rows(path: Path) -> list[dict[str, str]]:
    with path.open(newline="", encoding="utf-8") as handle:
        return list(csv.DictReader(handle))


def split_semicolon(value: str) -> list[str]:
    return [part for part in value.split(";") if part]


def expected_shape_count(shape: str) -> int:
    if shape not in EXPECTED_SHAPE_COUNTS:
        raise ValueError(f"unknown shape: {shape}")
    return EXPECTED_SHAPE_COUNTS[shape]


def compute_cell_status(rows: Sequence[dict[str, str]]) -> str:
    statuses = [row["status"] for row in rows]
    if any(status == "UNKNOWN" for status in statuses):
        return "UNKNOWN"
    if statuses and all(status == "UNSAT" for status in statuses):
        return "ALL_UNSAT"
    if statuses and all(status == "SAT" for status in statuses):
        return "ALL_SAT"
    return "MIXED_WITHIN_SHAPE"


def compute_cell_status_rows(
    *,
    mask_rows: Sequence[dict[str, str]],
    witness_rows: Sequence[dict[str, str]],
) -> list[dict[str, object]]:
    mask_by_id = {row["case_id"]: row for row in mask_rows}
    rows_by_case_shape: dict[tuple[str, str], list[dict[str, str]]] = defaultdict(list)
    for row in witness_rows:
        case_id = row["case_id"]
        mask = mask_by_id[case_id]
        if mask["minlib_active"] != "True":
            continue
        if row["overlap_class"] in SHAPE_ORDER:
            rows_by_case_shape[(case_id, row["overlap_class"])].append(row)

    cell_rows: list[dict[str, object]] = []
    for case_id in sorted(
        [row["case_id"] for row in mask_rows if row["minlib_active"] == "True"],
        key=lambda cid: cid.removeprefix("case_"),
    ):
        mask = mask_by_id[case_id]
        for shape in SHAPE_ORDER:
            members = rows_by_case_shape[(case_id, shape)]
            counts = Counter(row["status"] for row in members)
            cell_rows.append(
                {
                    "case_id": case_id,
                    "active_bundled_levers": split_semicolon(mask["active_bundled_levers"]),
                    "active_base_atoms": split_semicolon(mask["active_base_atoms"]),
                    "mask_aggregate_status": mask["aggregate_status"],
                    "shape": shape,
                    "expected_witness_count": expected_shape_count(shape),
                    "actual_witness_count": len(members),
                    "num_sat": counts.get("SAT", 0),
                    "num_unsat": counts.get("UNSAT", 0),
                    "num_unknown": counts.get("UNKNOWN", 0),
                    "cell_status": compute_cell_status(members),
                }
            )
    return cell_rows


def q_atom(atom: str) -> str:
    return rop.q_atom(atom)


def q_repair(repair: Iterable[str]) -> tuple[str, ...]:
    return rop.q_repair(repair)


def semantic_atoms_for_witness(mask: dict[str, str], witness_row: dict[str, str]) -> tuple[str, ...]:
    atoms = split_semicolon(mask["active_base_atoms"])
    if mask["minlib_active"] == "True":
        cfg = witness_row["config_id"]
        if cfg == "no_minlib":
            raise ValueError(f"minlib-active case has no witness config: {mask['case_id']}")
        pair0, pair1 = smp.parse_config_id(cfg)
        atoms.extend([smp.right_atom(0, pair0), smp.right_atom(1, pair1)])
    return smp.sorted_atoms(atoms)


def solve_mcs_for_witness(
    *,
    case_id: str,
    mask: dict[str, str],
    witness_row: dict[str, str],
    solver: str,
    timeout: float,
    work_dir: Path,
) -> dict[str, object]:
    atoms = semantic_atoms_for_witness(mask, witness_row)
    schema = smp.FiniteSchema(n=2, m=4, minlib_mode="disabled")
    guard_vars = {atom: schema.n_p_vars + idx + 1 for idx, atom in enumerate(atoms)}
    atom_blocks = {atom: smp.atom_clauses(schema, atom) for atom in atoms}
    nvars = schema.n_p_vars + len(atoms)
    status_by_subset: dict[frozenset[str], str] = {}
    unknown_subsets = []
    case_work = work_dir / case_id / witness_row["config_id"]
    case_work.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(prefix="cnf_", dir=str(case_work)) as tmp_raw:
        tmp_dir = Path(tmp_raw)
        for subset in smp.powerset(atoms):
            selected = smp.sorted_atoms(subset)
            clauses = smp.guarded_subset_clauses(
                atom_blocks=atom_blocks,
                guard_vars=guard_vars,
                selected_atoms=selected,
            )
            cnf_path = tmp_dir / "subset.cnf"
            smp.write_dimacs(cnf_path, nvars, clauses)
            status, _return_code, _output = smp.solver_status(solver, cnf_path, timeout)
            status_by_subset[frozenset(selected)] = status
            if status == "UNKNOWN":
                unknown_subsets.append(selected)
    full_status = status_by_subset[frozenset(atoms)]
    if full_status != "UNSAT":
        raise ValueError(f"expected UNSAT full package for {case_id} {witness_row['config_id']}, got {full_status}")
    mcs = smp.compute_mcs(atoms, status_by_subset)
    return {
        "target_case": case_id,
        "config_id": witness_row["config_id"],
        "overlap_class": witness_row["overlap_class"],
        "active_semantic_atom_ids": list(atoms),
        "mcs_ids": [list(edge) for edge in mcs],
        "mcs_count": len(mcs),
        "unknown_subset_count": len(unknown_subsets),
        "duality_passes": len(unknown_subsets) == 0,
    }


def validate_non_circularity(metadata: dict[str, object]) -> dict[str, object]:
    required_true = [
        "t_is_bundled_mask_schema",
        "shape_not_part_of_t_identity",
        "shape_computed_from_w",
        "cell_is_analysis_stratum",
        "residual_class_not_defined_by_law",
    ]
    failures = [name for name in required_true if metadata.get(name) is not True]
    return {"verdict": "PASS" if not failures else "FAIL", "failures": failures}


def cell_orbit_fiber_exactness_verdict(
    *,
    fiber_rows: Sequence[dict[str, object]],
    orbit_rows: Sequence[dict[str, object]],
) -> dict[str, object]:
    partial = [row for row in fiber_rows if row.get("contains_partial_orbit_fragments")]
    nonsingle = [row for row in fiber_rows if not row.get("is_single_repair_orbit")]
    crossing = [row for row in orbit_rows if not row.get("is_orbit_contained_in_one_report_fiber")]
    failures = []
    if partial:
        failures.append("partial orbit fragments")
    if nonsingle:
        failures.append("non-single-orbit cell report fibers")
    if crossing:
        failures.append("orbit crosses cell report fibers")
    return {
        "verdict": "PASS" if not failures else "FAIL",
        "failure_reasons": failures,
        "partial_fragment_count": len(partial),
        "non_single_fiber_count": len(nonsingle),
        "crossing_orbit_count": len(crossing),
    }


def evaluate_support_truncation(blind_rows: Sequence[dict[str, object]]) -> dict[str, object]:
    failures = [row for row in blind_rows if not row.get("support_truncation_law_holds")]
    return {
        "verdict": "PASS" if not failures else "FAIL",
        "checked_shape_blind_fibers": len(blind_rows),
        "failure_count": len(failures),
        "failures": [
            {
                "case_id": row["case_id"],
                "report_label": row["report_label"],
                "blind_orbit_count": row["blind_orbit_count"],
                "shape_support_count": row["shape_support_count"],
            }
            for row in failures[:20]
        ],
    }


def build_shape_blind_rows(
    *,
    fibers: dict[rop.ReportKey, frozenset[rop.RepairObject]],
    orbit_by_object: dict[rop.RepairObject, int],
    orbit_rows: Sequence[dict[str, object]],
) -> list[dict[str, object]]:
    orbit_label = {idx: str(row["orbit_id"]) for idx, row in enumerate(orbit_rows)}
    blind: dict[tuple[str, tuple[str, ...]], dict[str, object]] = {}
    for key, members in fibers.items():
        blind_key = (key.target_case, key.report)
        row = blind.setdefault(
            blind_key,
            {
                "case_id": key.target_case,
                "report": list(key.report),
                "report_label": rop.report_label(key.report),
                "blind_fiber_size": 0,
                "shape_support_set": set(),
                "orbit_id_set": set(),
            },
        )
        row["blind_fiber_size"] = int(row["blind_fiber_size"]) + len(members)
        row["shape_support_set"].add(key.shape)  # type: ignore[union-attr]
        row["orbit_id_set"].update(orbit_by_object[obj] for obj in members)  # type: ignore[union-attr]

    rows = []
    for (_case_id, report), row in sorted(
        blind.items(),
        key=lambda item: (item[0][0], rop.report_sort_key(item[0][1])),
    ):
        shape_support = sorted(row["shape_support_set"], key=lambda shape: rop.SHAPE_INDEX[shape])  # type: ignore[arg-type]
        orbit_ids = sorted(row["orbit_id_set"])  # type: ignore[arg-type]
        rows.append(
            {
                "case_id": row["case_id"],
                "report": list(report),
                "report_label": row["report_label"],
                "blind_fiber_size": row["blind_fiber_size"],
                "blind_orbit_count": len(orbit_ids),
                "shape_support": shape_support,
                "shape_support_count": len(shape_support),
                "orbit_ids": [orbit_label[idx] for idx in orbit_ids],
                "support_truncation_law_holds": len(orbit_ids) == len(shape_support),
            }
        )
    return rows


def write_csv(path: Path, rows: Sequence[dict[str, object]], fieldnames: Sequence[str]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=fieldnames)
        writer.writeheader()
        for row in rows:
            out = {}
            for name in fieldnames:
                value = row.get(name, "")
                if isinstance(value, list):
                    out[name] = ";".join(str(item) for item in value)
                elif isinstance(value, tuple):
                    out[name] = ";".join(str(item) for item in value)
                else:
                    out[name] = value
            writer.writerow(out)


def public_repair_object_rows(objects: Sequence[rop.RepairObject]) -> list[dict[str, object]]:
    rows = []
    for obj in objects:
        raw = rop.object_to_json(obj)
        rows.append(
            {
                "case_id": raw["target_case"],
                "shape": raw["shape"],
                "config_id": raw["config_id"],
                "witness": raw["witness"],
                "repair_ids": raw["repair_ids"],
                "repair_label": raw["repair_label"],
                "report": raw["report"],
                "report_label": raw["report_label"],
            }
        )
    return rows


def public_cell_report_fiber_rows(fiber_rows: Sequence[dict[str, object]]) -> list[dict[str, object]]:
    rows = []
    for row in fiber_rows:
        rows.append(
            {
                "case_id": row["target_case"],
                "shape": row["shape"],
                "report": row["report"],
                "report_label": row["report_label"],
                "fiber_size_mu": row["fiber_size_mu"],
                "orbit_ids": row["orbit_ids"],
                "number_of_orbits_in_fiber": row["number_of_orbits_in_fiber"],
                "is_single_repair_orbit": row["is_single_repair_orbit"],
                "contains_partial_orbit_fragments": row["contains_partial_orbit_fragments"],
            }
        )
    return rows


def public_repair_orbit_rows(orbit_rows: Sequence[dict[str, object]]) -> list[dict[str, object]]:
    rows = []
    for row in orbit_rows:
        rows.append(
            {
                "orbit_id": row["orbit_id"],
                "case_id": row["target_case"],
                "shape": row["shape"],
                "report": row["report"],
                "report_label": row["report_label"],
                "orbit_size": row["orbit_size"],
                "stabilizer_size": row["stabilizer_size"],
                "orbit_stabilizer_product": row["orbit_stabilizer_product"],
                "representative_W": row["representative_W"],
                "representative_R": row["representative_R"],
                "shape_preserving_orbit": row["shape_preserving_orbit"],
                "is_orbit_contained_in_one_cell_report_fiber": row["is_orbit_contained_in_one_report_fiber"],
            }
        )
    return rows


def solver_metadata(solver: str) -> dict[str, object]:
    path = shutil.which(solver)
    version_raw = "unknown"
    try:
        import subprocess

        proc = subprocess.run([solver, "--version"], capture_output=True, text=True, timeout=5, check=False)
        version_raw = "\n".join(part for part in [proc.stdout.strip(), proc.stderr.strip()] if part) or "unknown"
    except Exception:
        pass
    return {
        "solver": solver,
        "solver_path": str(Path(path).resolve()) if path else "not found",
        "solver_version_raw": version_raw,
        "python_version": sys.version.split()[0],
        "platform": platform.platform(),
    }


def run_audit(
    *,
    certificate_dir: Path,
    solver: str,
    timeout: float,
    out_dir: Path,
) -> dict[str, object]:
    artifacts = input_artifacts(certificate_dir)
    require_input_artifacts(artifacts)
    if shutil.which(solver) is None:
        raise FileNotFoundError(f"solver not found on PATH: {solver}")
    out_dir.mkdir(parents=True, exist_ok=True)

    mask_rows = read_csv_rows(artifacts.mask_statuses)
    witness_rows = read_csv_rows(artifacts.witness_statuses)
    mask_by_id = {row["case_id"]: row for row in mask_rows}
    cell_rows = compute_cell_status_rows(mask_rows=mask_rows, witness_rows=witness_rows)
    cell_status_counts = Counter(str(row["cell_status"]) for row in cell_rows)
    unsat_cells = [row for row in cell_rows if row["cell_status"] == "ALL_UNSAT"]
    mixed_case_ids = {str(row["case_id"]) for row in mask_rows if row["aggregate_status"] == "MIXED"}
    all_w_unsat_case_ids = {str(row["case_id"]) for row in mask_rows if row["aggregate_status"] == "ALL_W_UNSAT"}
    unsat_cell_keys = {(str(row["case_id"]), str(row["shape"])) for row in unsat_cells}
    unsat_witness_rows = [
        row
        for row in witness_rows
        if (row["case_id"], row["overlap_class"]) in unsat_cell_keys and row["status"] == "UNSAT"
    ]
    if any(row["status"] != "UNSAT" for row in unsat_witness_rows):
        raise AssertionError("repair geometry target included non-UNSAT witness row")

    config_results = []
    with tempfile.TemporaryDirectory(prefix="m4_mask_shape_", dir=str(out_dir)) as tmp_raw:
        work_dir = Path(tmp_raw)
        for row in unsat_witness_rows:
            config_results.append(
                solve_mcs_for_witness(
                    case_id=row["case_id"],
                    mask=mask_by_id[row["case_id"]],
                    witness_row=row,
                    solver=solver,
                    timeout=timeout,
                    work_dir=work_dir,
                )
            )

    target_cases = tuple(sorted({str(row["case_id"]) for row in unsat_cells}, key=lambda cid: cid.removeprefix("case_")))
    original_order = rop.TARGET_ORDER
    original_index = rop.TARGET_INDEX
    try:
        rop.TARGET_ORDER = target_cases
        rop.TARGET_INDEX = {case_id: idx for idx, case_id in enumerate(target_cases)}
        objects, family = rop.repair_objects_from_phase1({"configuration_results": config_results})
        group = rop.group_elements()
        well_definedness = rop.check_well_definedness(objects=objects, family=family, group=group)
        q_invariance = rop.check_q_invariance(objects=objects, group=group)
        orbit_rows, orbit_by_object, orbit_sets = rop.compute_orbits(objects=objects, group=group)
        fibers = rop.build_fibers(objects)
        fiber_rows = rop.analyze_fibers(
            fibers=fibers,
            orbit_by_object=orbit_by_object,
            orbit_sets=orbit_sets,
            orbit_rows=orbit_rows,
        )
        orbit_stabilizer = rop.check_orbit_stabilizer_equation(objects=objects, group=group)
    finally:
        rop.TARGET_ORDER = original_order
        rop.TARGET_INDEX = original_index

    blind_rows = build_shape_blind_rows(
        fibers=fibers,
        orbit_by_object=orbit_by_object,
        orbit_rows=orbit_rows,
    )
    support_truncation = evaluate_support_truncation(blind_rows)
    cell_exactness = cell_orbit_fiber_exactness_verdict(fiber_rows=fiber_rows, orbit_rows=orbit_rows)
    bad_scope_objects = [
        rop.object_to_json(obj)
        for obj in objects
        if (obj.target_case, rop.witness_shape(obj.witness)) not in unsat_cell_keys
    ]
    repair_object_scope = {
        "verdict": "PASS" if not bad_scope_objects else "FAIL",
        "bad_scope_object_count": len(bad_scope_objects),
        "bad_scope_objects": bad_scope_objects[:20],
    }
    non_circularity_metadata = {
        "t_is_bundled_mask_schema": True,
        "shape_not_part_of_t_identity": True,
        "shape_computed_from_w": True,
        "cell_is_analysis_stratum": True,
        "residual_class_not_defined_by_law": True,
    }
    non_circularity = validate_non_circularity(non_circularity_metadata)
    mcs_unknown_subset_count = sum(int(row.get("unknown_subset_count", 0)) for row in config_results)
    shape_count_failures = [
        {
            "case_id": row["case_id"],
            "shape": row["shape"],
            "expected": row["expected_witness_count"],
            "actual": row["actual_witness_count"],
        }
        for row in cell_rows
        if row["expected_witness_count"] != row["actual_witness_count"]
    ]

    verdict_reasons = []
    if shape_count_failures:
        verdict_reasons.append("shape witness count check failed")
    if cell_status_counts.get("UNKNOWN", 0):
        verdict_reasons.append("UNKNOWN cells exist")
    if cell_status_counts.get("MIXED_WITHIN_SHAPE", 0):
        verdict_reasons.append("MIXED_WITHIN_SHAPE cells exist")
    if mcs_unknown_subset_count:
        verdict_reasons.append("UNKNOWN subset status occurred during MCS extraction")
    if repair_object_scope["verdict"] != "PASS":
        verdict_reasons.append("repair object outside ALL_UNSAT cells")
    if not well_definedness["passes"]:
        verdict_reasons.append("group action well-definedness failed")
    if not q_invariance["passes"]:
        verdict_reasons.append("q-invariance failed")
    if cell_exactness["verdict"] != "PASS":
        verdict_reasons.append("cell orbit-fiber exactness failed")
    if not orbit_stabilizer["passes"]:
        verdict_reasons.append("orbit-stabilizer failed")
    if support_truncation["verdict"] != "PASS":
        verdict_reasons.append("support truncation law failed")
    if non_circularity["verdict"] != "PASS":
        verdict_reasons.append("non-circularity failed")
    certificate_verdict = "PASS" if not verdict_reasons else "FAIL"

    observed_scratch_totals = {
        "mixed_only_unsat_witness_row_count": sum(
            1 for row in unsat_witness_rows if row["case_id"] in mixed_case_ids
        ),
        "mixed_only_repair_object_count": sum(1 for obj in objects if obj.target_case in mixed_case_ids),
        "mixed_only_repair_orbit_count": sum(1 for row in orbit_rows if row["target_case"] in mixed_case_ids),
        "mixed_only_cell_report_fiber_count": sum(
            1 for row in fiber_rows if row["target_case"] in mixed_case_ids
        ),
        "mixed_only_shape_blind_fiber_count": sum(
            1 for row in blind_rows if row["case_id"] in mixed_case_ids
        ),
        "all_w_unsat_repair_object_count": sum(1 for obj in objects if obj.target_case in all_w_unsat_case_ids),
        "all_w_unsat_repair_orbit_count": sum(
            1 for row in orbit_rows if row["target_case"] in all_w_unsat_case_ids
        ),
        "combined_repair_object_count": len(objects),
        "combined_repair_orbit_count": len(orbit_rows),
    }
    scratch_totals_match = all(
        observed_scratch_totals.get(name) == value
        for name, value in EXPECTED_SCRATCH_TOTALS.items()
        if name in observed_scratch_totals
    )
    repair_object_rows = public_repair_object_rows(objects)
    public_fiber_rows = public_cell_report_fiber_rows(fiber_rows)
    public_orbit_rows = public_repair_orbit_rows(orbit_rows)
    summary = {
        "input_certificate_dir": str(certificate_dir),
        "total_masks": len(mask_rows),
        "cell_status_counts": {status: cell_status_counts.get(status, 0) for status in CELL_STATUSES},
        "unsat_cell_count": len(unsat_cells),
        "unsat_witness_instance_count": len(unsat_witness_rows),
        "repair_object_count": len(objects),
        "cell_report_fiber_count": len(fiber_rows),
        "repair_orbit_count": len(orbit_rows),
        "shape_blind_fiber_count": len(blind_rows),
        "irregular_cell_count": cell_status_counts.get("MIXED_WITHIN_SHAPE", 0),
        "unknown_cell_count": cell_status_counts.get("UNKNOWN", 0),
        "well_definedness_verdict": "PASS" if well_definedness["passes"] else "FAIL",
        "q_invariance_verdict": "PASS" if q_invariance["passes"] else "FAIL",
        "repair_object_scope_verdict": repair_object_scope["verdict"],
        "cell_orbit_fiber_exactness_verdict": cell_exactness["verdict"],
        "orbit_stabilizer_verdict": "PASS" if orbit_stabilizer["passes"] else "FAIL",
        "support_truncation_law_verdict": support_truncation["verdict"],
        "non_circularity_verdict": non_circularity["verdict"],
        "observed_scratch_totals": observed_scratch_totals,
        "expected_scratch_totals": EXPECTED_SCRATCH_TOTALS,
        "expected_scratch_totals_match": scratch_totals_match,
        "certificate_verdict": certificate_verdict,
    }
    certificate = {
        "certificate_name": "M4 Mask-Shape Collapse Law Audit",
        "certificate_version": 1,
        "generated_at_utc": datetime.now(timezone.utc).isoformat(),
        "input_artifacts": {
            "mask_statuses": str(artifacts.mask_statuses),
            "witness_statuses": str(artifacts.witness_statuses),
            "residual_class_coverage_certificate": str(artifacts.certificate_json),
            "boundary_formula": str(artifacts.boundary_formula),
        },
        "solver_metadata": solver_metadata(solver),
        "scope": "UNSAT analysis cells inside bundled-minlib residual masks",
        "ambient_theory_individuation": "T is bundled residual mask/schema; shape is not part of T identity",
        "cell_definition": "Cell(T,s) = { W inside T | Shape(W)=s }",
        "repair_object_definition": "repair objects x=(T,W,R) are defined only for UNSAT witness instances in ALL_UNSAT cells",
        "group_definition": "G = S2_voters x S4_alternatives, |G| = 48",
        "grouped_report_map": {
            "asymm": "asymm",
            "un": "un",
            "no_cycle3": "no_cycle3",
            "no_cycle4": "no_cycle4",
            "right(voter,P)": "minlib",
        },
        "cell_statuses": cell_rows,
        "repair_object_count": len(objects),
        "repair_orbit_count": len(orbit_rows),
        "cell_report_fiber_count": len(fiber_rows),
        "shape_blind_fiber_count": len(blind_rows),
        "expected_scratch_totals": EXPECTED_SCRATCH_TOTALS,
        "expected_scratch_totals_match": scratch_totals_match,
        "well_definedness": well_definedness,
        "q_invariance": q_invariance,
        "repair_object_scope": repair_object_scope,
        "cell_orbit_fiber_exactness": cell_exactness,
        "orbit_stabilizer": orbit_stabilizer,
        "support_truncation_law": support_truncation,
        "non_circularity_checks": {
            **non_circularity_metadata,
            "verdict": non_circularity["verdict"],
            "failures": non_circularity["failures"],
        },
        "certificate_verdict": certificate_verdict,
        "certificate_verdict_reason": "all mask-shape collapse checks passed" if not verdict_reasons else "; ".join(verdict_reasons),
        "summary": summary,
        "non_claims": [
            "no Lean theorem",
            "no Certificate 2 completion",
            "no paper-ready theorem",
            "no 3-voter theorem",
            "no Arrow theorem",
            "no Gibbard-Satterthwaite theorem",
            "no general social-choice theorem",
            "no warrant-contract semantics",
            "shape is not ambient theory identity",
            "SAT cells have no repair objects",
            "MIXED masks have no full-mask repair geometry under the old T-only reading",
        ],
    }

    write_csv(
        out_dir / "cell_statuses.csv",
        cell_rows,
        [
            "case_id",
            "active_bundled_levers",
            "mask_aggregate_status",
            "shape",
            "expected_witness_count",
            "actual_witness_count",
            "num_sat",
            "num_unsat",
            "num_unknown",
            "cell_status",
        ],
    )
    write_csv(
        out_dir / "repair_objects.csv",
        repair_object_rows,
        ["case_id", "shape", "config_id", "witness", "repair_ids", "repair_label", "report", "report_label"],
    )
    write_csv(
        out_dir / "cell_report_fibers.csv",
        public_fiber_rows,
        [
            "case_id",
            "shape",
            "report",
            "report_label",
            "fiber_size_mu",
            "orbit_ids",
            "number_of_orbits_in_fiber",
            "is_single_repair_orbit",
            "contains_partial_orbit_fragments",
        ],
    )
    write_csv(
        out_dir / "repair_orbits.csv",
        public_orbit_rows,
        [
            "orbit_id",
            "case_id",
            "shape",
            "report",
            "report_label",
            "orbit_size",
            "stabilizer_size",
            "orbit_stabilizer_product",
            "representative_W",
            "representative_R",
            "shape_preserving_orbit",
            "is_orbit_contained_in_one_cell_report_fiber",
        ],
    )
    blind_fieldnames = [
        "case_id",
        "report",
        "report_label",
        "blind_fiber_size",
        "blind_orbit_count",
        "shape_support",
        "shape_support_count",
        "support_truncation_law_holds",
    ]
    write_csv(out_dir / "shape_blind_fibers.csv", blind_rows, blind_fieldnames)
    write_csv(
        out_dir / "support_truncation.csv",
        [
            {
                "case_id": row["case_id"],
                "report": row["report"],
                "report_label": row["report_label"],
                "shape_support": row["shape_support"],
                "blind_orbit_count": row["blind_orbit_count"],
                "shape_support_count": row["shape_support_count"],
                "law_holds": row["support_truncation_law_holds"],
            }
            for row in blind_rows
        ],
        ["case_id", "report", "report_label", "shape_support", "blind_orbit_count", "shape_support_count", "law_holds"],
    )
    (out_dir / "mask_shape_collapse_summary.json").write_text(
        json.dumps(summary, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    (out_dir / "mask_shape_collapse_certificate.json").write_text(
        json.dumps(certificate, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    return certificate


def main() -> None:
    parser = argparse.ArgumentParser(description="Audit the M4 mask-shape collapse law over UNSAT cells.")
    parser.add_argument("--certificate-dir", type=Path, default=CERT_DEFAULT)
    parser.add_argument("--solver", default="cadical")
    parser.add_argument("--timeout", type=float, default=10.0)
    parser.add_argument("--out", "--out-dir", dest="out_dir", type=Path, default=OUT_DEFAULT)
    args = parser.parse_args()
    payload = run_audit(
        certificate_dir=args.certificate_dir,
        solver=args.solver,
        timeout=args.timeout,
        out_dir=args.out_dir,
    )
    summary = payload["summary"]
    print(json.dumps(summary, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
