#!/usr/bin/env python3
from __future__ import annotations

import unittest

import mask_shape_collapse_law_audit as audit


def witness_row(case_id: str, shape: str, status: str, idx: int) -> dict[str, str]:
    return {
        "case_id": case_id,
        "config_id": f"cfg_{idx}",
        "overlap_class": shape,
        "status": status,
    }


class MaskShapeCollapseLawAuditTests(unittest.TestCase):
    def test_cell_status_from_witness_rows(self) -> None:
        self.assertEqual(
            audit.compute_cell_status([witness_row("case_11111", "O2", "UNSAT", idx) for idx in range(6)]),
            "ALL_UNSAT",
        )
        self.assertEqual(
            audit.compute_cell_status([witness_row("case_11111", "O2", "SAT", idx) for idx in range(6)]),
            "ALL_SAT",
        )
        self.assertEqual(
            audit.compute_cell_status(
                [
                    witness_row("case_11111", "O2", "SAT", 0),
                    witness_row("case_11111", "O2", "UNSAT", 1),
                ]
            ),
            "MIXED_WITHIN_SHAPE",
        )
        self.assertEqual(
            audit.compute_cell_status(
                [
                    witness_row("case_11111", "O2", "SAT", 0),
                    witness_row("case_11111", "O2", "UNKNOWN", 1),
                ]
            ),
            "UNKNOWN",
        )

    def test_expected_shape_counts(self) -> None:
        self.assertEqual(audit.expected_shape_count("O2"), 6)
        self.assertEqual(audit.expected_shape_count("O3"), 24)
        self.assertEqual(audit.expected_shape_count("O4"), 6)
        with self.assertRaises(ValueError):
            audit.expected_shape_count("O5")

    def test_q_mapping(self) -> None:
        right = audit.smp.right_atom(1, (0, 2))
        self.assertEqual(audit.q_atom(right), "minlib")
        self.assertEqual(audit.q_atom("asymm"), "asymm")
        self.assertEqual(audit.q_repair(["un", right]), ("un", "minlib"))

    def test_shape_support_computation(self) -> None:
        obj_o2 = audit.rop.RepairObject(
            target_case="case_11111",
            witness=audit.rop.canonical_witness((0, 1), (0, 1)),
            repair=("asymm",),
        )
        obj_o3 = audit.rop.RepairObject(
            target_case="case_11111",
            witness=audit.rop.canonical_witness((0, 1), (0, 2)),
            repair=("un",),
        )
        fibers = {
            audit.rop.ReportKey("case_11111", "O2", ("minlib",)): frozenset({obj_o2}),
            audit.rop.ReportKey("case_11111", "O3", ("minlib",)): frozenset({obj_o3}),
        }
        rows = audit.build_shape_blind_rows(
            fibers=fibers,
            orbit_by_object={obj_o2: 0, obj_o3: 1},
            orbit_rows=[{"orbit_id": "orbit_000"}, {"orbit_id": "orbit_001"}],
        )
        self.assertEqual(len(rows), 1)
        self.assertEqual(rows[0]["case_id"], "case_11111")
        self.assertEqual(rows[0]["report"], ["minlib"])
        self.assertEqual(rows[0]["shape_support"], ["O2", "O3"])
        self.assertEqual(rows[0]["shape_support_count"], 2)
        self.assertEqual(rows[0]["blind_orbit_count"], 2)
        self.assertTrue(rows[0]["support_truncation_law_holds"])

    def test_support_truncation_law_evaluator(self) -> None:
        passing = audit.evaluate_support_truncation(
            [
                {
                    "case_id": "case_11111",
                    "report_label": "{minlib}",
                    "shape_support_count": 3,
                    "blind_orbit_count": 3,
                    "support_truncation_law_holds": True,
                }
            ]
        )
        self.assertEqual(passing["verdict"], "PASS")
        failing = audit.evaluate_support_truncation(
            [
                {
                    "case_id": "case_11111",
                    "report_label": "{minlib}",
                    "shape_support_count": 3,
                    "blind_orbit_count": 2,
                    "support_truncation_law_holds": False,
                }
            ]
        )
        self.assertEqual(failing["verdict"], "FAIL")
        self.assertEqual(failing["failure_count"], 1)

    def test_non_circularity_metadata_validator(self) -> None:
        good = {
            "t_is_bundled_mask_schema": True,
            "shape_not_part_of_t_identity": True,
            "shape_computed_from_w": True,
            "cell_is_analysis_stratum": True,
            "residual_class_not_defined_by_law": True,
        }
        self.assertEqual(audit.validate_non_circularity(good)["verdict"], "PASS")
        bad = {**good, "shape_not_part_of_t_identity": False}
        result = audit.validate_non_circularity(bad)
        self.assertEqual(result["verdict"], "FAIL")
        self.assertEqual(result["failures"], ["shape_not_part_of_t_identity"])

    def test_detects_partial_orbit_fragments_synthetically(self) -> None:
        result = audit.cell_orbit_fiber_exactness_verdict(
            fiber_rows=[
                {
                    "contains_partial_orbit_fragments": True,
                    "is_single_repair_orbit": True,
                }
            ],
            orbit_rows=[{"is_orbit_contained_in_one_report_fiber": True}],
        )
        self.assertEqual(result["verdict"], "FAIL")
        self.assertIn("partial orbit fragments", result["failure_reasons"])

    def test_detects_mixed_within_shape_synthetically(self) -> None:
        mask_rows = [
            {
                "case_id": "case_11111",
                "minlib_active": "True",
                "active_bundled_levers": "asymm;un;minlib;no_cycle3;no_cycle4",
                "active_base_atoms": "asymm;un;no_cycle3;no_cycle4",
                "aggregate_status": "MIXED",
            }
        ]
        witness_rows = [
            witness_row("case_11111", "O2", "SAT", 0),
            witness_row("case_11111", "O2", "UNSAT", 1),
            *[witness_row("case_11111", "O3", "SAT", idx) for idx in range(24)],
            *[witness_row("case_11111", "O4", "UNSAT", idx) for idx in range(6)],
        ]
        rows = audit.compute_cell_status_rows(mask_rows=mask_rows, witness_rows=witness_rows)
        o2 = next(row for row in rows if row["shape"] == "O2")
        self.assertEqual(o2["cell_status"], "MIXED_WITHIN_SHAPE")


if __name__ == "__main__":
    unittest.main()
