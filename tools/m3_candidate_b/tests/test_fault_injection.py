#!/usr/bin/env python3
"""Fault-injection regression tests for every mandatory Candidate B gate."""

import unittest
from pathlib import Path

from tools.m3_candidate_b.fault_injections import FAULTS, run_fault_suite


REPO_ROOT = Path(__file__).resolve().parents[3]
PACKAGE_ROOT = REPO_ROOT / "m3" / "candidate_b"


class CandidateBFaultInjectionTests(unittest.TestCase):
    def test_all_mandatory_faults_fail_closed(self) -> None:
        self.assertEqual(len(FAULTS), 15)
        results = run_fault_suite(PACKAGE_ROOT, REPO_ROOT)
        failures = [row for row in results if row["result"] != "PASS"]
        self.assertEqual(failures, [], failures)


if __name__ == "__main__":
    unittest.main()
