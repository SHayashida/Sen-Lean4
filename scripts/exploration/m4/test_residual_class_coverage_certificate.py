#!/usr/bin/env python3
from __future__ import annotations

import unittest

import residual_class_coverage_certificate as rccc


def synthetic_row(case_id: str, status: str) -> dict[str, object]:
    mask = rccc.mask_from_case_id(case_id)
    return {
        "case_id": mask.case_id,
        **{lever: int(mask.levers[lever]) for lever in rccc.BUNDLED_UNIVERSE},
        "aggregate_status": status,
    }


class ResidualClassCoverageCertificateTests(unittest.TestCase):
    def test_bundled_mask_to_case_id_mapping(self) -> None:
        mask = rccc.BundledMask(bits=(1, 1, 1, 0, 1))
        self.assertEqual(mask.case_id, "case_11101")
        self.assertEqual(mask.active_bundled_levers, ("asymm", "un", "minlib", "no_cycle4"))
        self.assertEqual(mask.active_base_atoms, ("asymm", "un", "no_cycle4"))

    def test_all_32_bundled_masks_are_enumerated(self) -> None:
        masks = rccc.enumerate_bundled_masks()
        self.assertEqual(len(masks), 32)
        self.assertEqual(len({mask.case_id for mask in masks}), 32)
        self.assertIn("case_00000", {mask.case_id for mask in masks})
        self.assertIn("case_11111", {mask.case_id for mask in masks})

    def test_minlib_inactive_instantiation_uses_no_rights_sentinel(self) -> None:
        mask = rccc.mask_from_case_id("case_11001")
        rows = rccc.witness_rows_for_mask(mask)
        self.assertEqual(len(rows), 1)
        row = rows[0]
        self.assertEqual(row["config_id"], "no_minlib")
        self.assertEqual(row["overlap_class"], "none")
        self.assertEqual(row["right_atom_voter0"], "none")
        self.assertEqual(row["right_atom_voter1"], "none")
        self.assertEqual(rccc.semantic_atoms_for_instance(mask, row), ("asymm", "un", "no_cycle4"))

    def test_minlib_active_instantiation_generates_two_rights_per_witness(self) -> None:
        mask = rccc.mask_from_case_id("case_11101")
        rows = rccc.witness_rows_for_mask(mask)
        self.assertEqual(len(rows), 36)
        for row in rows:
            atoms = rccc.semantic_atoms_for_instance(mask, row)
            rights = [atom for atom in atoms if atom.startswith("right:v")]
            self.assertEqual(len(rights), 2)
            self.assertTrue(any(atom.startswith("right:v0:") for atom in rights))
            self.assertTrue(any(atom.startswith("right:v1:") for atom in rights))

    def test_bundled_instantiation_never_generates_one_sided_rights_package(self) -> None:
        for mask in rccc.enumerate_bundled_masks():
            for row in rccc.witness_rows_for_mask(mask):
                atoms = rccc.semantic_atoms_for_instance(mask, row)
                rights = [atom for atom in atoms if atom.startswith("right:v")]
                self.assertIn(len(rights), (0, 2))

    def test_formula_evaluator_accepts_expected_boundary(self) -> None:
        rows = []
        for mask in rccc.enumerate_bundled_masks():
            expected_unsat = (
                mask.levers["asymm"]
                and mask.levers["un"]
                and mask.levers["minlib"]
                and mask.levers["no_cycle4"]
            )
            rows.append(synthetic_row(mask.case_id, "ALL_W_UNSAT" if expected_unsat else "ALL_W_SAT"))
        boundary = rccc.evaluate_boundary(rows)
        self.assertEqual(boundary["candidate_formula_A_result"]["verdict"], "PASS")
        self.assertEqual(boundary["candidate_formula_B_result"]["verdict"], "PASS")
        self.assertEqual(boundary["candidate_formula_C_result"]["verdict"], "PASS")
        self.assertEqual(boundary["actual_unsat_case_ids"], ["case_11101", "case_11111"])

    def test_formula_evaluator_rejects_no_cycle3_dependence(self) -> None:
        rows = []
        for mask in rccc.enumerate_bundled_masks():
            expected_unsat = mask.case_id == "case_11111"
            rows.append(synthetic_row(mask.case_id, "ALL_W_UNSAT" if expected_unsat else "ALL_W_SAT"))
        boundary = rccc.evaluate_boundary(rows)
        self.assertEqual(boundary["candidate_formula_C_result"]["verdict"], "FAIL")
        self.assertEqual(boundary["candidate_formula_B_result"]["verdict"], "FAIL")
        self.assertEqual(boundary["minimal_dnf_if_needed"], ["asymm and un and minlib and no_cycle3 and no_cycle4"])


if __name__ == "__main__":
    unittest.main()
