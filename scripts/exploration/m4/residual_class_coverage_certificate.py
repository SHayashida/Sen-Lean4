#!/usr/bin/env python3
"""Certificate 1 coverage check for the bundled-minlib M4 ResidualClass.

This script is exploratory and intentionally scoped to the M4 design layer. It
does not import or call the production ``minlib`` selector encoding. Bundled
``minlib`` is instantiated selector-free as a two-person rights package only
after a witness configuration is chosen.
"""

from __future__ import annotations

import argparse
import csv
import itertools
import json
import shutil
import sys
import tempfile
from collections import Counter
from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path
from typing import Iterable

import semantic_mus_precheck as smp

BUNDLED_UNIVERSE = ("asymm", "un", "minlib", "no_cycle3", "no_cycle4")
BASE_ATOMS = ("asymm", "un", "no_cycle3", "no_cycle4")
OUT_DEFAULT = Path("/tmp/sen_m4_residual_class_coverage_certificate")
AGGREGATE_STATUSES = ("ALL_W_UNSAT", "ALL_W_SAT", "MIXED", "UNKNOWN")


@dataclass(frozen=True)
class BundledMask:
    bits: tuple[int, int, int, int, int]

    @property
    def case_id(self) -> str:
        return "case_" + "".join(str(bit) for bit in self.bits)

    @property
    def levers(self) -> dict[str, bool]:
        return {lever: bool(self.bits[idx]) for idx, lever in enumerate(BUNDLED_UNIVERSE)}

    @property
    def active_bundled_levers(self) -> tuple[str, ...]:
        return tuple(lever for lever, active in self.levers.items() if active)

    @property
    def active_base_atoms(self) -> tuple[str, ...]:
        active = self.levers
        return tuple(atom for atom in BASE_ATOMS if active[atom])

    @property
    def minlib_active(self) -> bool:
        return self.levers["minlib"]


def enumerate_bundled_masks() -> list[BundledMask]:
    return [BundledMask(bits=bits) for bits in itertools.product((0, 1), repeat=len(BUNDLED_UNIVERSE))]


def mask_from_case_id(case_id: str) -> BundledMask:
    prefix = "case_"
    if not case_id.startswith(prefix):
        raise ValueError(f"expected case_ prefix: {case_id!r}")
    raw = case_id.removeprefix(prefix)
    if len(raw) != len(BUNDLED_UNIVERSE) or any(ch not in "01" for ch in raw):
        raise ValueError(f"invalid bundled case id: {case_id!r}")
    return BundledMask(bits=tuple(int(ch) for ch in raw))  # type: ignore[arg-type]


def witness_rows_for_mask(mask: BundledMask) -> list[dict[str, object]]:
    if not mask.minlib_active:
        return [
            {
                "config_id": "no_minlib",
                "overlap_class": "none",
                "right_atom_voter0": "none",
                "right_atom_voter1": "none",
                "right_atom_id_voter0": "none",
                "right_atom_id_voter1": "none",
                "rights_atom_ids": [],
            }
        ]
    rows: list[dict[str, object]] = []
    for pair0, pair1 in smp.witness_configs():
        r0 = smp.right_atom(0, pair0)
        r1 = smp.right_atom(1, pair1)
        rows.append(
            {
                "config_id": smp.config_id(pair0, pair1),
                "overlap_class": smp.overlap_class(pair0, pair1),
                "right_atom_voter0": smp.atom_label(r0),
                "right_atom_voter1": smp.atom_label(r1),
                "right_atom_id_voter0": r0,
                "right_atom_id_voter1": r1,
                "rights_atom_ids": [r0, r1],
            }
        )
    return rows


def semantic_atoms_for_instance(mask: BundledMask, witness_row: dict[str, object]) -> tuple[str, ...]:
    atoms: list[str] = list(mask.active_base_atoms)
    if mask.minlib_active:
        rights = witness_row["rights_atom_ids"]
        if not isinstance(rights, list) or len(rights) != 2:
            raise ValueError(f"bundled minlib must instantiate exactly two rights atoms: {rights!r}")
        atoms.extend(str(atom) for atom in rights)
    return smp.sorted_atoms(atoms)


def direct_atom_clauses(atoms: Iterable[str]) -> tuple[int, list[list[int]], dict[str, int]]:
    schema = smp.FiniteSchema(n=2, m=4, minlib_mode="disabled")
    clauses: list[list[int]] = []
    provenance: dict[str, int] = {}
    for atom in smp.sorted_atoms(atoms):
        block = smp.atom_clauses(schema, atom)
        provenance[smp.atom_label(atom)] = len(block)
        clauses.extend(block)
    return schema.n_p_vars, clauses, provenance


def solve_instance(
    *,
    mask: BundledMask,
    witness_row: dict[str, object],
    solver: str,
    timeout: float,
    work_dir: Path,
) -> dict[str, object]:
    atoms = semantic_atoms_for_instance(mask, witness_row)
    nvars, clauses, provenance = direct_atom_clauses(atoms)
    cnf_path = work_dir / f"{mask.case_id}__{witness_row['config_id']}.cnf"
    smp.write_dimacs(cnf_path, nvars, clauses)
    status, return_code, _solver_output = smp.solver_status(solver, cnf_path, timeout)
    return {
        "case_id": mask.case_id,
        "config_id": witness_row["config_id"],
        "overlap_class": witness_row["overlap_class"],
        "active_bundled_levers": list(mask.active_bundled_levers),
        "active_base_atoms": list(mask.active_base_atoms),
        "right_atom_voter0": witness_row["right_atom_voter0"],
        "right_atom_voter1": witness_row["right_atom_voter1"],
        "semantic_atom_ids": list(atoms),
        "semantic_atoms": [smp.atom_label(atom) for atom in atoms],
        "clause_provenance_counts": provenance,
        "status": status,
        "solver_return_code": return_code,
    }


def aggregate_status(statuses: Iterable[str]) -> str:
    values = list(statuses)
    if any(status == "UNKNOWN" for status in values):
        return "UNKNOWN"
    if all(status == "UNSAT" for status in values):
        return "ALL_W_UNSAT"
    if all(status == "SAT" for status in values):
        return "ALL_W_SAT"
    return "MIXED"


def build_mask_row(mask: BundledMask, rows: list[dict[str, object]]) -> dict[str, object]:
    counts = Counter(str(row["status"]) for row in rows)
    status = aggregate_status(str(row["status"]) for row in rows)
    return {
        "case_id": mask.case_id,
        **{lever: int(mask.levers[lever]) for lever in BUNDLED_UNIVERSE},
        "active_bundled_levers": list(mask.active_bundled_levers),
        "active_base_atoms": list(mask.active_base_atoms),
        "minlib_active": mask.minlib_active,
        "num_witness_instances": len(rows),
        "num_sat": counts.get("SAT", 0),
        "num_unsat": counts.get("UNSAT", 0),
        "num_unknown": counts.get("UNKNOWN", 0),
        "aggregate_status": status,
    }


def _formula_verdict(
    *,
    mask_rows: list[dict[str, object]],
    predicate,
    scope_predicate=lambda _row: True,
) -> dict[str, object]:
    scoped = [row for row in mask_rows if scope_predicate(row)]
    mixed = [row["case_id"] for row in scoped if row["aggregate_status"] == "MIXED"]
    unknown = [row["case_id"] for row in scoped if row["aggregate_status"] == "UNKNOWN"]
    mismatches = [
        row["case_id"]
        for row in scoped
        if (row["aggregate_status"] == "ALL_W_UNSAT") != bool(predicate(row))
    ]
    verdict = "PASS" if not mixed and not unknown and not mismatches else "FAIL"
    if not unknown and not mixed and mismatches:
        verdict = "FAIL"
    if (mixed or unknown) and not mismatches:
        verdict = "CONDITIONAL"
    return {
        "verdict": verdict,
        "checked_case_count": len(scoped),
        "mismatching_case_ids": mismatches,
        "mixed_case_ids": mixed,
        "unknown_case_ids": unknown,
    }


def evaluate_formula_a(mask_rows: list[dict[str, object]]) -> dict[str, object]:
    return _formula_verdict(
        mask_rows=mask_rows,
        scope_predicate=lambda row: row["asymm"] == 1 and row["un"] == 1,
        predicate=lambda row: row["minlib"] == 1 and row["no_cycle4"] == 1,
    )


def evaluate_formula_b(mask_rows: list[dict[str, object]]) -> dict[str, object]:
    return _formula_verdict(
        mask_rows=mask_rows,
        predicate=lambda row: (
            row["asymm"] == 1
            and row["un"] == 1
            and row["minlib"] == 1
            and row["no_cycle4"] == 1
        ),
    )


def evaluate_formula_c(mask_rows: list[dict[str, object]]) -> dict[str, object]:
    by_key: dict[tuple[int, int, int, int], list[dict[str, object]]] = {}
    for row in mask_rows:
        key = (int(row["asymm"]), int(row["un"]), int(row["minlib"]), int(row["no_cycle4"]))
        by_key.setdefault(key, []).append(row)
    mismatches = []
    mixed = [str(row["case_id"]) for row in mask_rows if row["aggregate_status"] == "MIXED"]
    unknown = [str(row["case_id"]) for row in mask_rows if row["aggregate_status"] == "UNKNOWN"]
    for key, rows in sorted(by_key.items()):
        statuses = {str(row["aggregate_status"]) for row in rows}
        case_ids = [str(row["case_id"]) for row in rows]
        if len(statuses) != 1:
            mismatches.append({"fixed_levers": list(key), "case_ids": case_ids, "aggregate_statuses": sorted(statuses)})
    verdict = "PASS" if not mismatches and not mixed and not unknown else "FAIL"
    if (mixed or unknown) and not mismatches:
        verdict = "CONDITIONAL"
    return {
        "verdict": verdict,
        "checked_pairs": len(by_key),
        "mismatches": mismatches,
        "mixed_case_ids": mixed,
        "unknown_case_ids": unknown,
    }


def _cube_matches(cube: tuple[int | None, ...], bits: tuple[int, ...]) -> bool:
    return all(part is None or part == bits[idx] for idx, part in enumerate(cube))


def _cube_to_text(cube: tuple[int | None, ...]) -> str:
    parts = []
    for idx, part in enumerate(cube):
        if part is None:
            continue
        lever = BUNDLED_UNIVERSE[idx]
        parts.append(lever if part == 1 else f"not {lever}")
    return "true" if not parts else " and ".join(parts)


def minimal_dnf(true_case_ids: Iterable[str]) -> list[str]:
    true_bits = {mask_from_case_id(case_id).bits for case_id in true_case_ids}
    if not true_bits:
        return []
    all_bits = [mask.bits for mask in enumerate_bundled_masks()]
    cubes: list[tuple[int | None, ...]] = []
    for cube in itertools.product((0, 1, None), repeat=len(BUNDLED_UNIVERSE)):
        covered_true = {bits for bits in true_bits if _cube_matches(cube, bits)}
        if not covered_true:
            continue
        covered_all = {bits for bits in all_bits if _cube_matches(cube, bits)}
        if covered_all.issubset(true_bits):
            cubes.append(cube)
    # Keep only prime implicants by removing cubes made strictly more specific
    # by another valid cube.
    prime = []
    for cube in cubes:
        literal_count = sum(part is not None for part in cube)
        if any(
            other != cube
            and sum(part is not None for part in other) <= literal_count
            and all(_cube_matches(other, bits) for bits in all_bits if _cube_matches(cube, bits))
            for other in cubes
        ):
            continue
        prime.append(cube)
    best_cover: tuple[tuple[int | None, ...], ...] | None = None
    best_key: tuple[int, int] | None = None
    for size in range(1, len(prime) + 1):
        for combo in itertools.combinations(prime, size):
            covered = {bits for bits in true_bits if any(_cube_matches(cube, bits) for cube in combo)}
            if covered != true_bits:
                continue
            key = (size, sum(sum(part is not None for part in cube) for cube in combo))
            if best_key is None or key < best_key:
                best_cover = combo
                best_key = key
        if best_cover is not None:
            break
    return [_cube_to_text(cube) for cube in (best_cover or ())]


def evaluate_boundary(mask_rows: list[dict[str, object]]) -> dict[str, object]:
    formula_a = evaluate_formula_a(mask_rows)
    formula_b = evaluate_formula_b(mask_rows)
    formula_c = evaluate_formula_c(mask_rows)
    actual_unsat = [str(row["case_id"]) for row in mask_rows if row["aggregate_status"] == "ALL_W_UNSAT"]
    mixed = [str(row["case_id"]) for row in mask_rows if row["aggregate_status"] == "MIXED"]
    unknown = [str(row["case_id"]) for row in mask_rows if row["aggregate_status"] == "UNKNOWN"]
    minlib_inactive_unsat = [
        str(row["case_id"])
        for row in mask_rows
        if row["minlib"] == 0 and row["aggregate_status"] == "ALL_W_UNSAT"
    ]
    minlib_inactive_mixed = [
        str(row["case_id"])
        for row in mask_rows
        if row["minlib"] == 0 and row["aggregate_status"] == "MIXED"
    ]
    minlib_inactive_unknown = [
        str(row["case_id"])
        for row in mask_rows
        if row["minlib"] == 0 and row["aggregate_status"] == "UNKNOWN"
    ]
    relevant_expected = ["case_11101", "case_11111"]
    relevant_verdict = "PASS" if actual_unsat == relevant_expected and not unknown and not mixed else "FAIL"
    if actual_unsat == relevant_expected and mixed and not unknown:
        relevant_verdict = "CONDITIONAL"
    return {
        "candidate_formula_A_result": formula_a,
        "candidate_formula_B_result": formula_b,
        "candidate_formula_C_result": formula_c,
        "actual_unsat_case_ids": actual_unsat,
        "actual_unsat_masks": [
            {lever: mask_from_case_id(case_id).levers[lever] for lever in BUNDLED_UNIVERSE}
            for case_id in actual_unsat
        ],
        "minimal_dnf_if_needed": None if formula_b["verdict"] == "PASS" else minimal_dnf(actual_unsat),
        "mixed_case_ids": mixed,
        "unknown_case_ids": unknown,
        "no_cycle3_independence_result": formula_c,
        "minlib_inactive_unsat_absence_result": {
            "verdict": (
                "PASS"
                if not minlib_inactive_unsat and not minlib_inactive_unknown and not minlib_inactive_mixed
                else "FAIL"
            ),
            "minlib_inactive_all_w_unsat_case_ids": minlib_inactive_unsat,
            "minlib_inactive_mixed_case_ids": minlib_inactive_mixed,
            "minlib_inactive_unknown_case_ids": minlib_inactive_unknown,
        },
        "relevant_unsat_coverage_result": {
            "verdict": relevant_verdict,
            "expected_case_ids": relevant_expected,
            "actual_case_ids": actual_unsat,
            "mixed_case_ids": mixed,
            "unknown_case_ids": unknown,
        },
    }


def certificate_verdict(boundary: dict[str, object]) -> tuple[str, str]:
    formula_a = boundary["candidate_formula_A_result"]  # type: ignore[index]
    formula_b = boundary["candidate_formula_B_result"]  # type: ignore[index]
    formula_c = boundary["candidate_formula_C_result"]  # type: ignore[index]
    minlib_absence = boundary["minlib_inactive_unsat_absence_result"]  # type: ignore[index]
    relevant = boundary["relevant_unsat_coverage_result"]  # type: ignore[index]
    unknown = boundary["unknown_case_ids"]  # type: ignore[index]
    mixed = boundary["mixed_case_ids"]  # type: ignore[index]
    if unknown:
        return "FAIL", "UNKNOWN status exists"
    required = [
        ("candidate formula A", formula_a["verdict"]),  # type: ignore[index]
        ("candidate formula B", formula_b["verdict"]),  # type: ignore[index]
        ("candidate formula C", formula_c["verdict"]),  # type: ignore[index]
        ("minlib-inactive UNSAT absence", minlib_absence["verdict"]),  # type: ignore[index]
        ("relevant UNSAT coverage", relevant["verdict"]),  # type: ignore[index]
    ]
    if all(verdict == "PASS" for _name, verdict in required):
        return "PASS", "all Certificate 1 coverage checks passed"
    reasons = []
    if mixed:
        reasons.append("MIXED status exists")
    reasons.extend(f"{name} is {verdict}" for name, verdict in required if verdict != "PASS")
    return "CONDITIONAL_PASS", "; ".join(reasons)


def write_mask_statuses(path: Path, mask_rows: list[dict[str, object]]) -> None:
    fieldnames = [
        "case_id",
        "asymm",
        "un",
        "minlib",
        "no_cycle3",
        "no_cycle4",
        "active_bundled_levers",
        "active_base_atoms",
        "minlib_active",
        "num_witness_instances",
        "num_sat",
        "num_unsat",
        "num_unknown",
        "aggregate_status",
    ]
    with path.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=fieldnames)
        writer.writeheader()
        for row in mask_rows:
            writer.writerow(
                {
                    **{name: row[name] for name in fieldnames if name not in {"active_bundled_levers", "active_base_atoms"}},
                    "active_bundled_levers": ";".join(row["active_bundled_levers"]),  # type: ignore[arg-type]
                    "active_base_atoms": ";".join(row["active_base_atoms"]),  # type: ignore[arg-type]
                }
            )


def write_witness_statuses(path: Path, witness_statuses: list[dict[str, object]]) -> None:
    fieldnames = [
        "case_id",
        "config_id",
        "overlap_class",
        "active_bundled_levers",
        "active_base_atoms",
        "right_atom_voter0",
        "right_atom_voter1",
        "status",
        "solver_return_code",
    ]
    with path.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=fieldnames)
        writer.writeheader()
        for row in witness_statuses:
            writer.writerow(
                {
                    "case_id": row["case_id"],
                    "config_id": row["config_id"],
                    "overlap_class": row["overlap_class"],
                    "active_bundled_levers": ";".join(row["active_bundled_levers"]),  # type: ignore[arg-type]
                    "active_base_atoms": ";".join(row["active_base_atoms"]),  # type: ignore[arg-type]
                    "right_atom_voter0": row["right_atom_voter0"],
                    "right_atom_voter1": row["right_atom_voter1"],
                    "status": row["status"],
                    "solver_return_code": row["solver_return_code"],
                }
            )


def run_certificate(out_dir: Path, solver: str, timeout: float) -> dict[str, object]:
    if shutil.which(solver) is None:
        raise FileNotFoundError(f"solver not found on PATH: {solver}")
    out_dir.mkdir(parents=True, exist_ok=True)
    masks = enumerate_bundled_masks()
    witness_statuses: list[dict[str, object]] = []
    mask_rows: list[dict[str, object]] = []
    with tempfile.TemporaryDirectory(prefix="cnf_", dir=str(out_dir)) as tmp_raw:
        work_dir = Path(tmp_raw)
        for mask in masks:
            rows = [
                solve_instance(
                    mask=mask,
                    witness_row=witness_row,
                    solver=solver,
                    timeout=timeout,
                    work_dir=work_dir,
                )
                for witness_row in witness_rows_for_mask(mask)
            ]
            witness_statuses.extend(rows)
            mask_rows.append(build_mask_row(mask, rows))

    boundary = evaluate_boundary(mask_rows)
    verdict, verdict_reason = certificate_verdict(boundary)
    status_counts = Counter(str(row["aggregate_status"]) for row in mask_rows)
    payload = {
        "certificate_name": "M4 Certificate 1: ResidualClass Coverage",
        "certificate_version": 1,
        "generated_at_utc": datetime.now(timezone.utc).isoformat(),
        "solver_metadata": smp.solver_metadata(solver),
        "bundled_universe": list(BUNDLED_UNIVERSE),
        "residual_class_individuation": {
            "scope": "bundled-minlib-aligned semantic ResidualClass",
            "T_identity": "bundled residual mask/schema",
            "W_identity": "internal fixed-witness parameter, not part of T",
        },
        "semantic_instantiation_rule": {
            "minlib_inactive": "no rights atoms instantiated; W is inert for satisfiability",
            "minlib_active": "for each W instantiate exactly right(voter0,P) and right(voter1,Q)",
            "one_sided_rights_packages": "not instantiated",
            "production_minlib_selector_encoding": "not imported or called",
        },
        "one_sided_split_rows_scope_status": "upstream split artifacts; not ambient M4 residual theories T",
        "full_split_universe_scope_status": "upstream representation artifact; not M4 ResidualClass",
        "total_masks": len(mask_rows),
        "total_witness_rows": len(witness_statuses),
        "aggregate_status_counts": {status: status_counts.get(status, 0) for status in AGGREGATE_STATUSES},
        "all_w_unsat_case_ids": [row["case_id"] for row in mask_rows if row["aggregate_status"] == "ALL_W_UNSAT"],
        "all_w_sat_case_ids": [row["case_id"] for row in mask_rows if row["aggregate_status"] == "ALL_W_SAT"],
        "mixed_case_ids": boundary["mixed_case_ids"],
        "unknown_case_ids": boundary["unknown_case_ids"],
        "core_formula_verdict": boundary["candidate_formula_B_result"],
        "finite_auditability_verdict": (
            "complete finite enumeration over the declared bundled-minlib-aligned ResidualClass"
            if verdict == "PASS"
            else "finite enumeration completed but Certificate 1 did not fully pass"
        ),
        "certificate_verdict": verdict,
        "certificate_verdict_reason": verdict_reason,
        "boundary_formula": boundary,
        "mask_statuses": mask_rows,
    }
    write_mask_statuses(out_dir / "mask_statuses.csv", mask_rows)
    write_witness_statuses(out_dir / "witness_statuses.csv", witness_statuses)
    (out_dir / "boundary_formula.json").write_text(
        json.dumps(boundary, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    (out_dir / "coverage_summary.json").write_text(
        json.dumps(
            {
                "certificate_verdict": verdict,
                "certificate_verdict_reason": verdict_reason,
                "total_masks": len(mask_rows),
                "total_witness_rows": len(witness_statuses),
                "aggregate_status_counts": payload["aggregate_status_counts"],
                "all_w_unsat_case_ids": payload["all_w_unsat_case_ids"],
                "mixed_case_ids": payload["mixed_case_ids"],
                "unknown_case_ids": payload["unknown_case_ids"],
                "candidate_formula_A_result": boundary["candidate_formula_A_result"],
                "candidate_formula_B_result": boundary["candidate_formula_B_result"],
                "candidate_formula_C_result": boundary["candidate_formula_C_result"],
            },
            indent=2,
            sort_keys=True,
        )
        + "\n",
        encoding="utf-8",
    )
    (out_dir / "residual_class_coverage_certificate.json").write_text(
        json.dumps(payload, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    return payload


def main() -> None:
    parser = argparse.ArgumentParser(description="Generate M4 ResidualClass coverage Certificate 1.")
    parser.add_argument("--solver", default="cadical")
    parser.add_argument("--timeout", type=float, default=10.0)
    parser.add_argument("--out", "--out-dir", dest="out_dir", type=Path, default=OUT_DEFAULT)
    args = parser.parse_args()
    payload = run_certificate(args.out_dir, args.solver, args.timeout)
    print(
        json.dumps(
            {
                "out_dir": str(args.out_dir),
                "certificate_verdict": payload["certificate_verdict"],
                "total_masks": payload["total_masks"],
                "total_witness_rows": payload["total_witness_rows"],
                "aggregate_status_counts": payload["aggregate_status_counts"],
                "all_w_unsat_case_ids": payload["all_w_unsat_case_ids"],
                "mixed_case_ids": payload["mixed_case_ids"],
                "unknown_case_ids": payload["unknown_case_ids"],
                "core_formula_verdict": payload["core_formula_verdict"],
            },
            indent=2,
            sort_keys=True,
        )
    )


if __name__ == "__main__":
    main()
