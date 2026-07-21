#!/usr/bin/env python3
"""Deterministic fault-injection suite for the Candidate B validator."""

from __future__ import annotations

import copy
import json
import shutil
import tempfile
from pathlib import Path
from typing import Any, Callable, Dict, List, Mapping, Tuple

from tools.m3_candidate_b.validate_candidate_b import (
    AuditFailure,
    git_blob_sha,
    sha256_bytes,
    validate_package,
)


Mutation = Callable[[Path], None]


def read_json(path: Path) -> Any:
    return json.loads(path.read_text(encoding="utf-8"))


def write_json(path: Path, value: Any) -> None:
    path.write_text(
        json.dumps(value, ensure_ascii=True, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )


def rebind_evidence(package: Path, relative: str) -> None:
    source_path = package / "source_artifacts.json"
    source = read_json(source_path)
    package_path = "evidence/" + relative
    data = (package / package_path).read_bytes()
    matching = [entry for entry in source["entries"] if entry["package_path"] == package_path]
    if len(matching) != 1:
        raise AssertionError("expected one source binding for " + package_path)
    matching[0]["content_sha256"] = sha256_bytes(data)
    matching[0]["source_blob_sha"] = git_blob_sha(data)
    write_json(source_path, source)


def mutate_status(package: Path, representation: str, case_id: str, status: str) -> None:
    atlas_rel = "%s/atlas.json" % representation
    atlas_path = package / "evidence" / atlas_rel
    atlas = read_json(atlas_path)
    rows = [row for row in atlas["cases"] if row["case_id"] == case_id]
    if len(rows) != 1:
        raise AssertionError("case not found: " + case_id)
    old = rows[0]["status"]
    rows[0]["status"] = status
    atlas["status_counts"][old] -= 1
    atlas["status_counts"][status] += 1
    write_json(atlas_path, atlas)
    rebind_evidence(package, atlas_rel)

    summary_rel = "%s/%s/summary.json" % (representation, case_id)
    summary_path = package / "evidence" / summary_rel
    summary = read_json(summary_path)
    summary["status"] = status
    write_json(summary_path, summary)
    rebind_evidence(package, summary_rel)

    comparison_path = package / "evidence" / "comparison.json"
    comparison = read_json(comparison_path)
    field = "%s_status" % representation
    id_field = "%s_case_id" % representation
    for row in comparison["mapped_cases"]:
        if row[id_field] == case_id:
            row[field] = status
            row["status_equal"] = row["bundled_status"] == row["split_status"]
    write_json(comparison_path, comparison)
    rebind_evidence(package, "comparison.json")


def mutate_comparison(package: Path, callback: Callable[[Dict[str, Any]], None]) -> None:
    path = package / "evidence" / "comparison.json"
    value = read_json(path)
    callback(value)
    write_json(path, value)
    rebind_evidence(package, "comparison.json")


def full_bundled_sat(package: Path) -> None:
    mutate_status(package, "bundled", "case_11101", "SAT")


def full_split_sat(package: Path) -> None:
    mutate_status(package, "split", "case_111101", "SAT")


def delete_mapped_row(package: Path) -> None:
    mutate_comparison(package, lambda value: value["mapped_cases"].pop())


def swap_case_id(package: Path) -> None:
    def mutation(value: Dict[str, Any]) -> None:
        value["mapped_cases"][0]["split_case_id"] = "case_100000"
    mutate_comparison(package, mutation)


def activate_no_cycle3(package: Path) -> None:
    path = package / "contract.json"
    value = read_json(path)
    value["scope"]["inactive_atoms"] = []
    value["scope"]["active_contract_atoms"].append("no_cycle3")
    write_json(path, value)


def delete_d0_precomputed(package: Path) -> None:
    def mutation(value: Dict[str, Any]) -> None:
        row = next(row for row in value["repair_comparison"] if row["bundled_case_id"] == "case_11101")
        row["split_min_repairs"].remove("decisive_voter0")
    mutate_comparison(package, mutation)


def add_fake_nonsingleton(package: Path) -> None:
    def mutation(value: Dict[str, Any]) -> None:
        row = next(row for row in value["repair_comparison"] if row["bundled_case_id"] == "case_11101")
        row["split_min_repairs"].append(["asymm", "un"])
    mutate_comparison(package, mutation)


def mutate_bundled_residual(package: Path) -> None:
    mutate_status(package, "bundled", "case_11001", "UNSAT")


def remove_d1_block(package: Path) -> None:
    path = package / "contract.json"
    value = read_json(path)
    value["block_map"]["minlib"] = ["decisive_voter0"]
    write_json(path, value)


def touch_all(package: Path) -> None:
    path = package / "contract.json"
    value = read_json(path)
    value["grouping"] = "touch-all"
    write_json(path, value)


def source_hash(package: Path) -> None:
    path = package / "source_artifacts.json"
    value = read_json(path)
    value["entries"][0]["content_sha256"] = "0" * 64
    write_json(path, value)


def theorem_sha(package: Path) -> None:
    path = package / "theorem_binding.json"
    value = read_json(path)
    value["source_commit"] = "0" * 40
    write_json(path, value)


def duplicate_mapped_row(package: Path) -> None:
    def mutation(value: Dict[str, Any]) -> None:
        value["mapped_cases"].append(copy.deepcopy(value["mapped_cases"][0]))
    mutate_comparison(package, mutation)


def unknown_contract_atom(package: Path) -> None:
    path = package / "contract.json"
    value = read_json(path)
    value["scope"]["active_contract_atoms"][0] = "unknown_atom"
    write_json(path, value)


def bit_order_change(package: Path) -> None:
    path = package / "case_schema.json"
    value = read_json(path)
    value["bundled"]["bit_order"][0:2] = reversed(value["bundled"]["bit_order"][0:2])
    write_json(path, value)


FAULTS: List[Tuple[str, str, str, Mutation]] = [
    ("fully_active_bundled_status", "fully_active_bundled", "not UNSAT", full_bundled_sat),
    ("fully_active_split_status", "fully_active_split", "not UNSAT", full_split_sat),
    ("delete_mapped_row", "residual_faithfulness", "exactly 32", delete_mapped_row),
    ("swap_case_id", "residual_faithfulness", "block map", swap_case_id),
    ("activate_no_cycle3", "contract_schema", "scope differs", activate_no_cycle3),
    ("delete_d0_precomputed", "precomputed_claim_crosscheck", "differs", delete_d0_precomputed),
    ("add_fake_nonsingleton", "precomputed_claim_crosscheck", "unknown or non-singleton", add_fake_nonsingleton),
    ("mutate_bundled_residual", "residual_faithfulness", "status mismatch", mutate_bundled_residual),
    ("remove_d1_block", "contract_schema", "block map differs", remove_d1_block),
    ("touch_all_grouping", "contract_schema", "touch-any", touch_all),
    ("source_content_hash", "source_artifact_binding", "content hash mismatch", source_hash),
    ("theorem_source_sha", "theorem_binding", "source commit changed", theorem_sha),
    ("duplicate_mapped_row", "residual_faithfulness", "exactly 32", duplicate_mapped_row),
    ("unknown_contract_atom", "contract_schema", "scope differs", unknown_contract_atom),
    ("bit_order_change", "case_schema", "case schema changed", bit_order_change),
]


def run_fault_suite(package_root: Path, repo_root: Path) -> List[Mapping[str, Any]]:
    results: List[Mapping[str, Any]] = []
    for name, expected_gate, expected_message, mutation in FAULTS:
        with tempfile.TemporaryDirectory(prefix="candidate-b-fault-") as temporary:
            package = Path(temporary) / "candidate_b"
            shutil.copytree(str(package_root), str(package))
            mutation(package)
            observed_code = 0
            observed_gate = ""
            observed_message = "validator unexpectedly passed"
            try:
                validate_package(
                    package / "contract.json",
                    package / "case_schema.json",
                    package / "source_artifacts.json",
                    package / "evidence",
                    package / "theorem_binding.json",
                    package / "generated",
                    repo_root,
                    verify_git_source=False,
                )
            except AuditFailure as failure:
                observed_code = 1
                observed_gate = failure.gate
                observed_message = failure.message
            passed = (
                observed_code == 1
                and observed_gate == expected_gate
                and expected_message in observed_message
            )
            results.append({
                "fault": name,
                "expected_exit_code": 1,
                "expected_gate": expected_gate,
                "expected_message_contains": expected_message,
                "observed_exit_code": observed_code,
                "observed_gate": observed_gate,
                "observed_message": observed_message,
                "result": "PASS" if passed else "FAIL",
            })
    return results

