#!/usr/bin/env python3
from __future__ import annotations

import json
import unittest

import repair_orbit_precheck as rop


def phase1_fixture_payload() -> dict[str, object]:
    config_results = []
    for target in rop.smp.TARGET_RESIDUALS:
        for pair0, pair1 in rop.smp.witness_configs():
            shape = rop.smp.overlap_class(pair0, pair1)
            r0 = rop.smp.right_atom(0, pair0)
            r1 = rop.smp.right_atom(1, pair1)
            subset_count = 2 ** (len(target.base_atoms) + 2)
            if target.case_id == "case_11101":
                mus_count = 1
                if shape == "O2":
                    mcs = [("asymm",), (r0,), (r1,)]
                else:
                    mcs = [("un",), ("no_cycle4",), (r0,), (r1,)]
            else:
                if shape == "O2":
                    mus_count = 1
                    mcs = [("asymm",), (r0,), (r1,)]
                elif shape == "O3":
                    mus_count = 2
                    mcs = [("un",), (r0,), (r1,), ("no_cycle3", "no_cycle4")]
                else:
                    mus_count = 1
                    mcs = [("un",), ("no_cycle4",), (r0,), (r1,)]
            config_results.append(
                {
                    "target_case": target.case_id,
                    "config_id": rop.smp.config_id(pair0, pair1),
                    "mcs_ids": [list(edge) for edge in mcs],
                    "mcs_count": len(mcs),
                    "mus_count": mus_count,
                    "subset_count": subset_count,
                    "unknown_subset_count": 0,
                    "duality_passes": True,
                }
            )
    return {
        "subset_status_count": sum(int(row["subset_count"]) for row in config_results),
        "configuration_results": config_results,
        "voter_swap": {"passes": True},
        "o2_o3_o4": {"alternative_relabeling_passes": True},
        "shape_comparison": {
            "all_representative_signatures_stable": True,
            "all_targets_have_shape_structural_difference": True,
        },
    }


class RepairOrbitPrecheckTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.payload = phase1_fixture_payload()
        cls.analysis = rop.analyze_phase1_payload(cls.payload, phase1_source={"mode": "fixture"})

    def test_group_size(self) -> None:
        self.assertEqual(len(rop.group_elements()), 48)
        self.assertEqual(self.analysis["group"]["size"], 48)

    def test_voter_swap_on_witness_configurations(self) -> None:
        tau = rop.GroupElement(voter_perm=(1, 0), alt_perm=(0, 1, 2, 3))
        witness = rop.canonical_witness((0, 1), (2, 3))
        self.assertEqual(rop.apply_group_to_witness(tau, witness), rop.canonical_witness((2, 3), (0, 1)))

    def test_alternative_permutation_on_unordered_pairs(self) -> None:
        perm = (3, 2, 1, 0)
        self.assertEqual(rop.apply_alt_to_pair((0, 2), perm), (1, 3))
        self.assertEqual(rop.apply_alt_to_pair((3, 0), perm), (0, 3))

    def test_product_action_on_repair_object(self) -> None:
        tau = rop.GroupElement(voter_perm=(1, 0), alt_perm=(0, 1, 2, 3))
        obj = rop.RepairObject(
            target_case="case_11101",
            witness=rop.canonical_witness((0, 1), (2, 3)),
            repair=rop.smp.sorted_atoms(["no_cycle4", rop.smp.right_atom(0, (0, 1))]),
        )
        image = rop.apply_group_to_object(tau, obj)
        self.assertEqual(image.target_case, "case_11101")
        self.assertEqual(image.witness, rop.canonical_witness((2, 3), (0, 1)))
        self.assertEqual(
            image.repair,
            rop.smp.sorted_atoms(["no_cycle4", rop.smp.right_atom(1, (0, 1))]),
        )

    def test_shape_preservation_under_group_action(self) -> None:
        group = rop.group_elements()
        for witness in (rop.canonical_witness((0, 1), (0, 1)), rop.canonical_witness((0, 1), (0, 2)), rop.canonical_witness((0, 1), (2, 3))):
            shape = rop.witness_shape(witness)
            for element in group:
                self.assertEqual(rop.witness_shape(rop.apply_group_to_witness(element, witness)), shape)

    def test_action_well_definedness_on_synthetic_repair_family(self) -> None:
        objects = []
        family: dict[tuple[str, rop.WitnessConfig], set[tuple[str, ...]]] = {}
        for pair in rop.smp.PAIR_ORDER:
            witness = rop.canonical_witness(pair, pair)
            repairs = [
                ("asymm",),
                (rop.smp.right_atom(0, pair),),
                (rop.smp.right_atom(1, pair),),
            ]
            family[("case_11101", witness)] = {rop.smp.sorted_atoms(repair) for repair in repairs}
            for repair in repairs:
                objects.append(
                    rop.RepairObject(
                        target_case="case_11101",
                        witness=witness,
                        repair=rop.smp.sorted_atoms(repair),
                    )
                )
        check = rop.check_well_definedness(
            objects=objects,
            family={key: frozenset(value) for key, value in family.items()},
            group=rop.group_elements(),
        )
        self.assertTrue(check["passes"])

    def test_grouped_report_map_q(self) -> None:
        right = rop.smp.right_atom(0, (0, 1))
        self.assertEqual(rop.q_atom(right), "minlib")
        self.assertEqual(rop.q_atom("no_cycle3"), "no_cycle3")
        self.assertEqual(rop.q_repair(["un", right]), ("un", "minlib"))

    def test_q_invariance_under_group_action(self) -> None:
        self.assertTrue(self.analysis["q_invariance"]["passes"])

    def test_orbit_stabilizer_equation_for_every_repair_object(self) -> None:
        orbit_stabilizer = self.analysis["orbit_stabilizer"]
        self.assertTrue(orbit_stabilizer["passes"])
        self.assertEqual(orbit_stabilizer["checked_repair_objects"], 276)

    def test_report_fiber_construction(self) -> None:
        fibers = self.analysis["report_fibers"]
        self.assertEqual(len(fibers), 16)
        o2_minlib = next(
            row for row in fibers
            if row["target_case"] == "case_11101" and row["shape"] == "O2" and row["report"] == ["minlib"]
        )
        self.assertEqual(o2_minlib["fiber_size_mu"], 12)
        self.assertEqual(o2_minlib["number_of_orbits_in_fiber"], 1)

    def test_orbit_partition_of_a_fiber(self) -> None:
        o3_minlib = next(
            row for row in self.analysis["report_fibers"]
            if row["target_case"] == "case_11101" and row["shape"] == "O3" and row["report"] == ["minlib"]
        )
        self.assertTrue(o3_minlib["is_single_repair_orbit"])
        self.assertTrue(o3_minlib["is_stable_union_of_complete_orbits"])
        self.assertFalse(o3_minlib["contains_partial_orbit_fragments"])
        self.assertEqual(o3_minlib["orbit_sizes_inside_fiber"], [48])

    def test_no_obsolete_phase1_terminology_reused_as_repair_orbit_result(self) -> None:
        text = json.dumps(self.analysis, sort_keys=True)
        self.assertNotIn("provisional_voter_indexed_semantic_repair_multiplicity", text)
        self.assertNotIn("mcs_voter_index_multiplicity", text)
        self.assertIn("formal_mu", text)

    def test_formal_mu_is_fiber_cardinality_not_phase1_multiplicity(self) -> None:
        for row in self.analysis["report_fibers"]:
            self.assertEqual(row["formal_mu_definition"], "fiber cardinality")
        o2_minlib = next(
            row for row in self.analysis["report_fibers"]
            if row["target_case"] == "case_11111" and row["shape"] == "O2" and row["report"] == ["minlib"]
        )
        self.assertEqual(o2_minlib["fiber_size_mu"], 12)
        self.assertNotEqual(o2_minlib["fiber_size_mu"], 2)


if __name__ == "__main__":
    unittest.main()
