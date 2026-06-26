#!/usr/bin/env python3
from __future__ import annotations

import unittest

import semantic_mus_precheck as smp


class SemanticMusPrecheckTests(unittest.TestCase):
    def test_pair_canonicalization(self) -> None:
        self.assertEqual(smp.canonical_pair(2, 0), (0, 2))
        self.assertEqual(smp.canonical_pair(1, 3), (1, 3))
        with self.assertRaises(ValueError):
            smp.canonical_pair(1, 1)

    def test_voter_swap(self) -> None:
        atom = smp.right_atom(0, (3, 1))
        self.assertEqual(atom, "right:v0:1-3")
        self.assertEqual(smp.voter_swap_atom(atom), "right:v1:1-3")
        self.assertEqual(smp.swap_config_id("v0_01__v1_23"), "v0_23__v1_01")

    def test_mus_minimality(self) -> None:
        a, b, c = "asymm", "un", "no_cycle4"
        status = {
            frozenset(): "SAT",
            frozenset({a}): "SAT",
            frozenset({b}): "SAT",
            frozenset({c}): "SAT",
            frozenset({a, b}): "UNSAT",
            frozenset({a, c}): "SAT",
            frozenset({b, c}): "UNSAT",
            frozenset({a, b, c}): "UNSAT",
        }
        self.assertEqual(smp.compute_mus(status), [(a, b), (b, c)])

    def test_mcs_mus_hitting_set_duality(self) -> None:
        universe = ("a", "b", "c")
        mus = [("a", "b"), ("b", "c")]
        hitting_sets = smp.minimal_hitting_sets(universe, mus)
        self.assertEqual(hitting_sets, [("b",), ("a", "c")])
        status = {}
        for subset in smp.powerset(universe):
            retained = frozenset(subset)
            status[retained] = "UNSAT" if any(set(edge).issubset(retained) for edge in mus) else "SAT"
        self.assertEqual(smp.compute_mcs(universe, status), hitting_sets)

    def test_shape_signature_records_structural_components(self) -> None:
        r0 = smp.right_atom(0, (0, 1))
        r1 = smp.right_atom(1, (0, 2))
        sig = smp.shape_signature(
            mus=[("un", "no_cycle4", r0, r1)],
            mcs=[("un",), ("no_cycle4",), (r0,), (r1,)],
            rights_atoms=(r0, r1),
            swap_row={"full_stabilizer": ["id"], "proper_stabilizer": [], "orbit_size": 2},
        )
        self.assertEqual(sig["mus_cardinality_multiset"], [4])
        self.assertEqual(sig["mcs_cardinality_multiset"], [1, 1, 1, 1])
        self.assertEqual(sig["minimal_rights_only_hitting_set_family"], [["R0"], ["R1"]])
        self.assertIn(["R0", 1], sig["mus_hypergraph_degree_sequence"])

    def test_structural_signature_key_ignores_swap_profile(self) -> None:
        r0 = smp.right_atom(0, (0, 1))
        r1 = smp.right_atom(1, (0, 1))
        sig1 = smp.shape_signature(
            mus=[("asymm", r0, r1)],
            mcs=[("asymm",), (r0,), (r1,)],
            rights_atoms=(r0, r1),
            swap_row={"full_stabilizer": ["id"], "proper_stabilizer": [], "orbit_size": 2},
        )
        sig2 = dict(sig1)
        sig2["voter_swap_stabilizer_profile"] = {
            "full_stabilizer": ["id", "tau"],
            "proper_stabilizer": ["tau"],
        }
        sig2["repair_orbit_size_profile"] = {"orbit_size": 1}
        self.assertEqual(smp.structural_signature_key(sig1), smp.structural_signature_key(sig2))


if __name__ == "__main__":
    unittest.main()
