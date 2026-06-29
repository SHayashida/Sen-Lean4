#!/usr/bin/env python3
from __future__ import annotations

import unittest

import certificate2_phase_diagram_checker as c2


def cell(case_id: str, shape: str, status: str) -> dict[str, str]:
    expected = str(c2.EXPECTED_SHAPE_COUNTS[shape])
    return {
        "case_id": case_id,
        "shape": shape,
        "expected_witness_count": expected,
        "actual_witness_count": expected,
        "num_sat": expected if status == "ALL_SAT" else "0",
        "num_unsat": expected if status == "ALL_UNSAT" else "0",
        "num_unknown": "0",
        "cell_status": status,
    }


def witness_rows(case_id: str, shape: str, status: str, count: int | None = None) -> list[dict[str, str]]:
    n = c2.EXPECTED_SHAPE_COUNTS[shape] if count is None else count
    return [
        {
            "case_id": case_id,
            "config_id": f"{case_id}_{shape}_{idx}",
            "overlap_class": shape,
            "status": status,
        }
        for idx in range(n)
    ]


def mask_rows() -> list[dict[str, str]]:
    return [{"case_id": f"case_{idx:05b}", "minlib_active": "True"} for idx in range(16)]


def full_cell_rows() -> list[dict[str, str]]:
    rows = []
    for mask in mask_rows():
        for shape in c2.SHAPE_ORDER:
            rows.append(cell(mask["case_id"], shape, "ALL_SAT"))
    return rows


class Certificate2PhaseDiagramCheckerTests(unittest.TestCase):
    def test_cell_coverage_counting(self) -> None:
        result = c2.analyze_cell_coverage(mask_rows=mask_rows(), cell_rows=full_cell_rows())
        self.assertEqual(result["verdict"], "PASS")
        self.assertEqual(result["total_cells"], 48)
        self.assertEqual(result["status_counts"]["ALL_SAT"], 48)

    def test_expected_shape_membership_detection(self) -> None:
        rows = full_cell_rows()[:-1]
        result = c2.analyze_cell_coverage(mask_rows=mask_rows(), cell_rows=rows)
        self.assertEqual(result["verdict"], "FAIL")
        self.assertTrue(result["shape_membership_failures"])

    def test_repair_empty_predicate(self) -> None:
        cells = [cell("case_00100", "O2", "ALL_SAT")]
        witnesses = witness_rows("case_00100", "O2", "SAT")
        result = c2.evaluate_repair_empty_cells(
            cell_rows=cells,
            witness_rows=witnesses,
            repair_rows=[],
            repair_objects_guarded_by_unsat=True,
        )
        self.assertEqual(result["verdict"], "PASS")
        self.assertTrue(result["rows"][0]["repair_empty_holds"])

    def test_unsat_guarded_repair_object_policy(self) -> None:
        cells = [cell("case_00100", "O2", "ALL_SAT")]
        witnesses = witness_rows("case_00100", "O2", "SAT")
        result = c2.evaluate_repair_empty_cells(
            cell_rows=cells,
            witness_rows=witnesses,
            repair_rows=[],
            repair_objects_guarded_by_unsat=False,
        )
        self.assertEqual(result["verdict"], "FAIL")
        self.assertFalse(result["rows"][0]["constructor_guard"])

    def test_detects_repair_object_in_sat_cell(self) -> None:
        cells = [cell("case_00100", "O2", "ALL_SAT")]
        witnesses = witness_rows("case_00100", "O2", "SAT")
        repairs = [{"case_id": "case_00100", "shape": "O2", "config_id": "x", "repair_ids": "asymm", "report": "asymm"}]
        result = c2.evaluate_repair_empty_cells(
            cell_rows=cells,
            witness_rows=witnesses,
            repair_rows=repairs,
            repair_objects_guarded_by_unsat=False,
        )
        self.assertEqual(result["verdict"], "FAIL")
        self.assertEqual(result["rows"][0]["repair_object_count"], 1)

    def test_detects_sat_witness_inside_all_unsat_cell(self) -> None:
        cells = [cell("case_11111", "O3", "ALL_UNSAT")]
        witnesses = witness_rows("case_11111", "O3", "SAT")
        result = c2.evaluate_unsat_cells(cell_rows=cells, witness_rows=witnesses, repair_rows=[])
        self.assertEqual(result["verdict"], "FAIL")
        self.assertEqual(result["rows"][0]["sat_witness_count"], c2.EXPECTED_SHAPE_COUNTS["O3"])

    def test_detects_unsat_witness_inside_all_sat_cell(self) -> None:
        cells = [cell("case_00100", "O4", "ALL_SAT")]
        witnesses = witness_rows("case_00100", "O4", "UNSAT")
        result = c2.evaluate_repair_empty_cells(
            cell_rows=cells,
            witness_rows=witnesses,
            repair_rows=[],
            repair_objects_guarded_by_unsat=True,
        )
        self.assertEqual(result["verdict"], "FAIL")
        self.assertEqual(result["rows"][0]["unsat_witness_count"], c2.EXPECTED_SHAPE_COUNTS["O4"])

    def test_orbit_fiber_exactness_evaluator(self) -> None:
        all_unsat = {("case_11111", "O2")}
        fibers = [
            {
                "case_id": "case_11111",
                "shape": "O2",
                "report": "minlib",
                "fiber_size_mu": "12",
                "orbit_ids": "orbit_000",
                "number_of_orbits_in_fiber": "1",
                "is_single_repair_orbit": "True",
                "contains_partial_orbit_fragments": "False",
            }
        ]
        orbits = [
            {
                "orbit_id": "orbit_000",
                "case_id": "case_11111",
                "shape": "O2",
                "orbit_size": "12",
                "stabilizer_size": "4",
                "orbit_stabilizer_product": "48",
                "shape_preserving_orbit": "True",
                "is_orbit_contained_in_one_cell_report_fiber": "True",
            }
        ]
        result = c2.evaluate_orbit_fiber_exactness(
            fiber_rows=fibers,
            orbit_rows=orbits,
            all_unsat_keys=all_unsat,
        )
        self.assertEqual(result["verdict"], "PASS")
        bad = [{**fibers[0], "contains_partial_orbit_fragments": "True"}]
        self.assertEqual(
            c2.evaluate_orbit_fiber_exactness(fiber_rows=bad, orbit_rows=orbits, all_unsat_keys=all_unsat)["verdict"],
            "FAIL",
        )

    def test_support_truncation_evaluator(self) -> None:
        cell_by_key = {
            ("case_11111", "O2"): cell("case_11111", "O2", "ALL_UNSAT"),
            ("case_11111", "O3"): cell("case_11111", "O3", "ALL_UNSAT"),
        }
        blind = [
            {
                "case_id": "case_11111",
                "report": "minlib",
                "blind_fiber_size": "60",
                "blind_orbit_count": "2",
                "shape_support": "O2;O3",
                "shape_support_count": "2",
                "support_truncation_law_holds": "True",
            }
        ]
        support = [
            {
                "case_id": "case_11111",
                "report": "minlib",
                "shape_support": "O2;O3",
                "blind_orbit_count": "2",
                "shape_support_count": "2",
                "law_holds": "True",
            }
        ]
        result = c2.evaluate_support_truncation(
            shape_blind_rows=blind,
            support_rows=support,
            cell_by_key=cell_by_key,
        )
        self.assertEqual(result["verdict"], "PASS")
        bad_blind = [{**blind[0], "blind_orbit_count": "1"}]
        self.assertEqual(
            c2.evaluate_support_truncation(
                shape_blind_rows=bad_blind,
                support_rows=support,
                cell_by_key=cell_by_key,
            )["verdict"],
            "FAIL",
        )

    def test_non_circularity_metadata_validator(self) -> None:
        metadata = {
            "t_is_bundled_mask_schema": True,
            "shape_computed_from_w": True,
            "cell_is_analysis_stratum": True,
            "residual_class_not_defined_by_collapse_behavior": True,
            "sat_cells_empty_because_sat": True,
            "unsat_cells_included_because_unsat": True,
            "repair_objects_guarded_by_unsat": True,
        }
        self.assertEqual(c2.validate_non_circularity_metadata(metadata)["verdict"], "PASS")
        metadata["repair_objects_guarded_by_unsat"] = False
        self.assertEqual(c2.validate_non_circularity_metadata(metadata)["verdict"], "FAIL")

    def test_certificate3_4_absorption_metadata(self) -> None:
        metadata = c2.absorption_metadata()
        self.assertEqual(c2.validate_absorption_metadata(metadata)["verdict"], "PASS")
        bad = {**metadata, "certificate3_independent_stage": True}
        self.assertEqual(c2.validate_absorption_metadata(bad)["verdict"], "FAIL")


if __name__ == "__main__":
    unittest.main()
