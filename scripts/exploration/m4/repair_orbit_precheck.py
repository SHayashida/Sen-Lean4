#!/usr/bin/env python3
"""M4 Phase 2 repair-orbit and grouped-report precheck.

This exploratory script is intentionally isolated from the production encoder.
It consumes the selector-free Phase 1 semantic MUS/MCS output and computes
repair objects, the natural S2 x S4 action, grouped-report fibers, formal
report-fiber multiplicity, repair orbits, and stabilizers.
"""

from __future__ import annotations

import argparse
import csv
import itertools
import json
import sys
from collections import defaultdict
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable, Sequence

SCRIPT_DIR = Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

REPO_ROOT = Path(__file__).resolve().parents[3]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

import semantic_mus_precheck as smp  # noqa: E402

Pair = tuple[int, int]
WitnessConfig = tuple[Pair, Pair]

OUT_DEFAULT = Path("/tmp/sen_m4_repair_orbit")
PHASE1_OUT_DEFAULT = Path("/tmp/sen_m4_semantic_mus")
PHASE1_JSON_DEFAULT = PHASE1_OUT_DEFAULT / "precheck_results.json"

TARGET_ORDER = tuple(target.case_id for target in smp.TARGET_RESIDUALS)
TARGET_INDEX = {case_id: idx for idx, case_id in enumerate(TARGET_ORDER)}
SHAPE_ORDER = ("O2", "O3", "O4")
SHAPE_INDEX = {shape: idx for idx, shape in enumerate(SHAPE_ORDER)}
REPORT_ORDER = ("asymm", "un", "minlib", "no_cycle3", "no_cycle4")
REPORT_INDEX = {atom: idx for idx, atom in enumerate(REPORT_ORDER)}

EXPECTED_PHASE1_COUNTS = {
    "subset_status_count": 3456,
    "unknown_subset_count": 0,
    "semantic_mus_total": 96,
    "semantic_mcs_total": 276,
}

NON_CLAIMS = [
    "no Lean theorem",
    "no M4 final theorem",
    "no 3-voter result",
    "no Arrow result",
    "no Gibbard-Satterthwaite result",
    "no general social-choice theorem",
    "no warrant-contract semantics",
    "no Delegated Warrant Preservation theorem",
    "no paper-ready claim",
    "no semantic-to-CNF correctness theorem",
]


@dataclass(frozen=True)
class GroupElement:
    """Element of S2_voters x S4_alternatives.

    The permutations are maps from old index to new index.
    """

    voter_perm: tuple[int, int]
    alt_perm: tuple[int, int, int, int]


@dataclass(frozen=True)
class RepairObject:
    """Semantic repair object x = (target_case, W, R)."""

    target_case: str
    witness: WitnessConfig
    repair: tuple[str, ...]


@dataclass(frozen=True)
class ReportKey:
    """Shape-indexed grouped-report fiber key."""

    target_case: str
    shape: str
    report: tuple[str, ...]


def canonical_witness(pair0: Pair, pair1: Pair) -> WitnessConfig:
    return (smp.canonical_pair(*pair0), smp.canonical_pair(*pair1))


def witness_from_config_id(config_id: str) -> WitnessConfig:
    return canonical_witness(*smp.parse_config_id(config_id))


def witness_config_id(witness: WitnessConfig) -> str:
    return smp.config_id(witness[0], witness[1])


def witness_shape(witness: WitnessConfig) -> str:
    return smp.overlap_class(witness[0], witness[1])


def pair_label(pair: Pair) -> str:
    pair = smp.canonical_pair(*pair)
    return f"{{{pair[0]},{pair[1]}}}"


def witness_label(witness: WitnessConfig) -> str:
    return f"((voter0,{pair_label(witness[0])}),(voter1,{pair_label(witness[1])}))"


def repair_label(repair: Iterable[str]) -> str:
    labels = [smp.atom_label(atom) for atom in smp.sorted_atoms(repair)]
    return "{" + ", ".join(labels) + "}"


def report_label(report: Iterable[str]) -> str:
    report_tuple = sort_report_atoms(report)
    return "{" + ", ".join(report_tuple) + "}"


def target_sort_index(target_case: str) -> int:
    return TARGET_INDEX.get(target_case, len(TARGET_INDEX))


def report_sort_key(report: Sequence[str]) -> tuple[tuple[int, str], ...]:
    return tuple((REPORT_INDEX.get(atom, len(REPORT_INDEX)), atom) for atom in report)


def sort_report_atoms(atoms: Iterable[str]) -> tuple[str, ...]:
    return tuple(sorted(set(atoms), key=lambda atom: (REPORT_INDEX.get(atom, len(REPORT_INDEX)), atom)))


def repair_sort_key(obj: RepairObject) -> tuple[object, ...]:
    return (
        target_sort_index(obj.target_case),
        SHAPE_INDEX[witness_shape(obj.witness)],
        witness_config_id(obj.witness),
        len(obj.repair),
        tuple(smp.atom_sort_key(atom) for atom in obj.repair),
    )


def report_key_sort_key(key: ReportKey) -> tuple[object, ...]:
    return (
        target_sort_index(key.target_case),
        SHAPE_INDEX[key.shape],
        report_sort_key(key.report),
    )


def group_element_label(element: GroupElement) -> str:
    voter = "id" if element.voter_perm == (0, 1) else "tau"
    alt = "".join(str(value) for value in element.alt_perm)
    return f"{voter}:{alt}"


def group_element_sort_key(element: GroupElement) -> tuple[int, tuple[int, int, int, int]]:
    return (0 if element.voter_perm == (0, 1) else 1, element.alt_perm)


def group_elements() -> tuple[GroupElement, ...]:
    elements = []
    for voter_perm in ((0, 1), (1, 0)):
        for alt_perm in itertools.permutations(smp.ALT_VALUES):
            elements.append(GroupElement(voter_perm=voter_perm, alt_perm=alt_perm))
    return tuple(sorted(elements, key=group_element_sort_key))


IDENTITY = GroupElement(voter_perm=(0, 1), alt_perm=(0, 1, 2, 3))


def compose_group(left: GroupElement, right: GroupElement) -> GroupElement:
    """Return left after right, as maps from old index to new index."""

    return GroupElement(
        voter_perm=(
            left.voter_perm[right.voter_perm[0]],
            left.voter_perm[right.voter_perm[1]],
        ),
        alt_perm=(
            left.alt_perm[right.alt_perm[0]],
            left.alt_perm[right.alt_perm[1]],
            left.alt_perm[right.alt_perm[2]],
            left.alt_perm[right.alt_perm[3]],
        ),
    )


def subgroup_closure(generators: Iterable[GroupElement]) -> frozenset[GroupElement]:
    closure = {IDENTITY}
    gens = set(generators)
    changed = True
    while changed:
        changed = False
        for a in tuple(closure):
            for b in tuple(gens | closure):
                for candidate in (compose_group(a, b), compose_group(b, a)):
                    if candidate not in closure:
                        closure.add(candidate)
                        changed = True
    return frozenset(closure)


def greedy_generators(subgroup: Iterable[GroupElement]) -> tuple[GroupElement, ...]:
    subgroup_set = set(subgroup)
    generators: list[GroupElement] = []
    generated = subgroup_closure(generators)
    for element in sorted(subgroup_set - {IDENTITY}, key=group_element_sort_key):
        if element not in generated:
            generators.append(element)
            generated = subgroup_closure(generators)
        if generated == subgroup_set:
            break
    return tuple(generators)


def apply_alt_to_pair(pair: Pair, alt_perm: tuple[int, int, int, int]) -> Pair:
    return smp.canonical_pair(alt_perm[pair[0]], alt_perm[pair[1]])


def apply_group_to_witness(element: GroupElement, witness: WitnessConfig) -> WitnessConfig:
    assigned: dict[int, Pair] = {}
    for old_voter, pair in enumerate(witness):
        new_voter = element.voter_perm[old_voter]
        assigned[new_voter] = apply_alt_to_pair(pair, element.alt_perm)
    return canonical_witness(assigned[0], assigned[1])


def apply_group_to_atom(element: GroupElement, atom: str) -> str:
    if not smp.is_right_atom(atom):
        return atom
    voter, pair = smp.parse_right_atom(atom)
    new_voter = element.voter_perm[voter]
    new_pair = apply_alt_to_pair(pair, element.alt_perm)
    return smp.right_atom(new_voter, new_pair)


def apply_group_to_repair(element: GroupElement, repair: Iterable[str]) -> tuple[str, ...]:
    return smp.sorted_atoms(apply_group_to_atom(element, atom) for atom in repair)


def apply_group_to_object(element: GroupElement, obj: RepairObject) -> RepairObject:
    return RepairObject(
        target_case=obj.target_case,
        witness=apply_group_to_witness(element, obj.witness),
        repair=apply_group_to_repair(element, obj.repair),
    )


def q_atom(atom: str) -> str:
    if smp.is_right_atom(atom):
        return "minlib"
    if atom in smp.BASE_ORDER:
        return atom
    raise ValueError(f"unknown semantic atom for q: {atom!r}")


def q_repair(repair: Iterable[str]) -> tuple[str, ...]:
    return sort_report_atoms(q_atom(atom) for atom in repair)


def q_object(obj: RepairObject) -> ReportKey:
    return ReportKey(
        target_case=obj.target_case,
        shape=witness_shape(obj.witness),
        report=q_repair(obj.repair),
    )


def object_to_json(obj: RepairObject) -> dict[str, object]:
    report = q_repair(obj.repair)
    return {
        "target_case": obj.target_case,
        "shape": witness_shape(obj.witness),
        "config_id": witness_config_id(obj.witness),
        "witness": witness_label(obj.witness),
        "repair_ids": list(obj.repair),
        "repair": [smp.atom_label(atom) for atom in obj.repair],
        "repair_label": repair_label(obj.repair),
        "report": list(report),
        "report_label": report_label(report),
    }


def report_key_to_json(key: ReportKey) -> dict[str, object]:
    return {
        "target_case": key.target_case,
        "shape": key.shape,
        "report": list(key.report),
        "report_label": report_label(key.report),
    }


def load_phase1_payload(
    *,
    phase1_json: Path,
    phase1_out_dir: Path,
    solver: str,
    timeout: float,
    force_regenerate: bool,
) -> tuple[dict[str, object], dict[str, object]]:
    if force_regenerate or not phase1_json.exists():
        payload = smp.run_precheck(phase1_out_dir, solver, timeout)
        source = {
            "mode": "regenerated",
            "path": str(phase1_out_dir / "precheck_results.json"),
            "solver": solver,
            "timeout": timeout,
        }
        return payload, source
    with phase1_json.open("r", encoding="utf-8") as handle:
        payload = json.load(handle)
    return payload, {
        "mode": "reused",
        "path": str(phase1_json),
        "solver": solver,
        "timeout": timeout,
    }


def validate_phase1_payload(payload: dict[str, object]) -> dict[str, object]:
    config_results = payload.get("configuration_results", [])
    if not isinstance(config_results, list):
        raise ValueError("Phase 1 payload has no configuration_results list")
    subset_status_count = int(payload.get("subset_status_count", -1))
    unknown_subset_count = sum(int(row.get("unknown_subset_count", 0)) for row in config_results)
    semantic_mus_total = sum(int(row.get("mus_count", 0)) for row in config_results)
    semantic_mcs_total = sum(int(row.get("mcs_count", 0)) for row in config_results)
    duality_passes = all(bool(row.get("duality_passes")) for row in config_results)
    voter_swap_passes = bool(payload.get("voter_swap", {}).get("passes"))  # type: ignore[union-attr]
    shape = payload.get("shape_comparison", {})
    if not isinstance(shape, dict):
        shape = {}
    shape_verdict_passes = (
        bool(shape.get("all_representative_signatures_stable"))
        and bool(shape.get("all_targets_have_shape_structural_difference"))
        and bool(payload.get("o2_o3_o4", {}).get("alternative_relabeling_passes"))  # type: ignore[union-attr]
    )
    expected_checks = {
        "subset_status_count": subset_status_count == EXPECTED_PHASE1_COUNTS["subset_status_count"],
        "unknown_subset_count": unknown_subset_count == EXPECTED_PHASE1_COUNTS["unknown_subset_count"],
        "semantic_mus_total": semantic_mus_total == EXPECTED_PHASE1_COUNTS["semantic_mus_total"],
        "semantic_mcs_total": semantic_mcs_total == EXPECTED_PHASE1_COUNTS["semantic_mcs_total"],
        "mus_mcs_duality": duality_passes,
        "o2_o3_o4_shape_verdict": shape_verdict_passes,
        "voter_swap_equivariance": voter_swap_passes,
    }
    validation = {
        "expected_counts": EXPECTED_PHASE1_COUNTS,
        "observed_counts": {
            "subset_status_count": subset_status_count,
            "unknown_subset_count": unknown_subset_count,
            "semantic_mus_total": semantic_mus_total,
            "semantic_mcs_total": semantic_mcs_total,
        },
        "checks": expected_checks,
        "passes": all(expected_checks.values()),
    }
    if not validation["passes"]:
        failures = [name for name, passed in expected_checks.items() if not passed]
        raise ValueError(f"Phase 1 validation failed: {', '.join(failures)}")
    return validation


def repair_objects_from_phase1(
    payload: dict[str, object],
) -> tuple[list[RepairObject], dict[tuple[str, WitnessConfig], frozenset[tuple[str, ...]]]]:
    config_results = payload["configuration_results"]
    if not isinstance(config_results, list):
        raise ValueError("Phase 1 payload has invalid configuration_results")
    objects: list[RepairObject] = []
    family: dict[tuple[str, WitnessConfig], set[tuple[str, ...]]] = defaultdict(set)
    for row in config_results:
        if not isinstance(row, dict):
            raise ValueError(f"invalid configuration row: {row!r}")
        target_case = str(row["target_case"])
        if target_case not in TARGET_INDEX:
            continue
        witness = witness_from_config_id(str(row["config_id"]))
        for repair_raw in row["mcs_ids"]:  # type: ignore[index]
            repair = smp.sorted_atoms(str(atom) for atom in repair_raw)
            obj = RepairObject(target_case=target_case, witness=witness, repair=repair)
            objects.append(obj)
            family[(target_case, witness)].add(repair)
    frozen_family = {key: frozenset(value) for key, value in family.items()}
    return sorted(objects, key=repair_sort_key), frozen_family


def check_well_definedness(
    *,
    objects: Sequence[RepairObject],
    family: dict[tuple[str, WitnessConfig], frozenset[tuple[str, ...]]],
    group: Sequence[GroupElement],
) -> dict[str, object]:
    witness_keys = set(family)
    failures: list[dict[str, object]] = []
    shape_failures: list[dict[str, object]] = []
    for obj in objects:
        for element in group:
            image = apply_group_to_object(element, obj)
            image_key = (image.target_case, image.witness)
            if image_key not in witness_keys:
                failures.append(
                    {
                        "kind": "missing_witness",
                        "element": group_element_label(element),
                        "source": object_to_json(obj),
                        "image": object_to_json(image),
                    }
                )
                continue
            if image.repair not in family[image_key]:
                failures.append(
                    {
                        "kind": "missing_repair",
                        "element": group_element_label(element),
                        "source": object_to_json(obj),
                        "image": object_to_json(image),
                    }
                )
            if witness_shape(obj.witness) != witness_shape(image.witness):
                shape_failures.append(
                    {
                        "element": group_element_label(element),
                        "source": object_to_json(obj),
                        "image": object_to_json(image),
                    }
                )
    return {
        "passes": not failures and not shape_failures,
        "checked_repair_objects": len(objects),
        "checked_group_elements": len(group),
        "checked_action_pairs": len(objects) * len(group),
        "witness_configuration_membership_passes": not any(f["kind"] == "missing_witness" for f in failures),
        "repair_family_membership_passes": not any(f["kind"] == "missing_repair" for f in failures),
        "shape_preservation_passes": not shape_failures,
        "failure_count": len(failures) + len(shape_failures),
        "failures": failures[:20],
        "shape_failures": shape_failures[:20],
    }


def check_q_invariance(
    *,
    objects: Sequence[RepairObject],
    group: Sequence[GroupElement],
) -> dict[str, object]:
    failures = []
    for obj in objects:
        source_key = q_object(obj)
        for element in group:
            image = apply_group_to_object(element, obj)
            image_key = q_object(image)
            if image_key != source_key:
                failures.append(
                    {
                        "element": group_element_label(element),
                        "source": object_to_json(obj),
                        "source_report": report_key_to_json(source_key),
                        "image": object_to_json(image),
                        "image_report": report_key_to_json(image_key),
                    }
                )
    return {
        "passes": not failures,
        "checked_action_pairs": len(objects) * len(group),
        "failure_count": len(failures),
        "failures": failures[:20],
    }


def compute_orbits(
    *,
    objects: Sequence[RepairObject],
    group: Sequence[GroupElement],
) -> tuple[list[dict[str, object]], dict[RepairObject, int], dict[int, frozenset[RepairObject]]]:
    object_set = set(objects)
    unseen = set(objects)
    orbit_rows: list[dict[str, object]] = []
    orbit_by_object: dict[RepairObject, int] = {}
    orbit_sets: dict[int, frozenset[RepairObject]] = {}

    while unseen:
        rep = min(unseen, key=repair_sort_key)
        orbit = frozenset(apply_group_to_object(element, rep) for element in group)
        if not orbit.issubset(object_set):
            missing = sorted(orbit - object_set, key=repair_sort_key)
            raise ValueError(f"group orbit left repair object universe at {object_to_json(missing[0])}")
        orbit_id = len(orbit_rows)
        stabilizer = tuple(element for element in group if apply_group_to_object(element, rep) == rep)
        generators = greedy_generators(stabilizer)
        reports = sorted({q_repair(obj.repair) for obj in orbit}, key=report_sort_key)
        report_keys = sorted({q_object(obj) for obj in orbit}, key=report_key_sort_key)
        orbit_shape_set = sorted({witness_shape(obj.witness) for obj in orbit}, key=lambda shape: SHAPE_INDEX[shape])
        row = {
            "orbit_id": f"orbit_{orbit_id:03d}",
            "target_case": rep.target_case,
            "shape": witness_shape(rep.witness),
            "representative": object_to_json(rep),
            "representative_W": witness_label(rep.witness),
            "representative_R": repair_label(rep.repair),
            "report": list(q_repair(rep.repair)),
            "report_label": report_label(q_repair(rep.repair)),
            "orbit_size": len(orbit),
            "stabilizer_size": len(stabilizer),
            "stabilizer_generators": [group_element_label(element) for element in generators],
            "stabilizer_elements": [group_element_label(element) for element in sorted(stabilizer, key=group_element_sort_key)],
            "all_reports_appearing_in_orbit": [report_label(report) for report in reports],
            "is_orbit_contained_in_one_report_fiber": len(report_keys) == 1,
            "shape_set": orbit_shape_set,
            "shape_preserving_orbit": len(orbit_shape_set) == 1,
            "orbit_stabilizer_product": len(orbit) * len(stabilizer),
        }
        orbit_rows.append(row)
        orbit_sets[orbit_id] = orbit
        for obj in orbit:
            orbit_by_object[obj] = orbit_id
        unseen -= orbit

    return orbit_rows, orbit_by_object, orbit_sets


def check_orbit_stabilizer_equation(
    *,
    objects: Sequence[RepairObject],
    group: Sequence[GroupElement],
) -> dict[str, object]:
    failures = []
    for obj in objects:
        orbit = {apply_group_to_object(element, obj) for element in group}
        stabilizer = [element for element in group if apply_group_to_object(element, obj) == obj]
        if len(orbit) * len(stabilizer) != len(group):
            failures.append(
                {
                    "object": object_to_json(obj),
                    "orbit_size": len(orbit),
                    "stabilizer_size": len(stabilizer),
                    "group_size": len(group),
                }
            )
    return {
        "passes": not failures,
        "checked_repair_objects": len(objects),
        "group_size": len(group),
        "failure_count": len(failures),
        "failures": failures[:20],
    }


def build_fibers(objects: Sequence[RepairObject]) -> dict[ReportKey, frozenset[RepairObject]]:
    fibers: dict[ReportKey, set[RepairObject]] = defaultdict(set)
    for obj in objects:
        fibers[q_object(obj)].add(obj)
    return {key: frozenset(value) for key, value in fibers.items()}


def analyze_fibers(
    *,
    fibers: dict[ReportKey, frozenset[RepairObject]],
    orbit_by_object: dict[RepairObject, int],
    orbit_sets: dict[int, frozenset[RepairObject]],
    orbit_rows: Sequence[dict[str, object]],
) -> list[dict[str, object]]:
    orbit_row_by_id = {idx: row for idx, row in enumerate(orbit_rows)}
    rows: list[dict[str, object]] = []
    for key in sorted(fibers, key=report_key_sort_key):
        members = fibers[key]
        orbit_ids = sorted({orbit_by_object[obj] for obj in members})
        partial_orbits = []
        orbit_sizes_inside = []
        stabilizer_sizes = []
        for orbit_id in orbit_ids:
            intersection = members & orbit_sets[orbit_id]
            orbit_sizes_inside.append(len(intersection))
            stabilizer_sizes.append(int(orbit_row_by_id[orbit_id]["stabilizer_size"]))
            if intersection and intersection != orbit_sets[orbit_id]:
                partial_orbits.append(
                    {
                        "orbit_id": orbit_row_by_id[orbit_id]["orbit_id"],
                        "orbit_size": len(orbit_sets[orbit_id]),
                        "intersection_size": len(intersection),
                    }
                )
        representative_objects = sorted(members, key=repair_sort_key)[:3]
        row = {
            **report_key_to_json(key),
            "fiber_size_mu": len(members),
            "formal_mu_definition": "fiber cardinality",
            "number_of_orbits_in_fiber": len(orbit_ids),
            "orbit_ids": [str(orbit_row_by_id[orbit_id]["orbit_id"]) for orbit_id in orbit_ids],
            "orbit_sizes_inside_fiber": orbit_sizes_inside,
            "stabilizer_size_multiset": sorted(stabilizer_sizes),
            "is_single_repair_orbit": len(orbit_ids) == 1 and not partial_orbits,
            "is_stable_union_of_complete_orbits": not partial_orbits,
            "contains_partial_orbit_fragments": bool(partial_orbits),
            "partial_orbit_fragments": partial_orbits,
            "representative_repair_objects": [object_to_json(obj) for obj in representative_objects],
        }
        rows.append(row)
    return rows


def object_counts(
    *,
    objects: Sequence[RepairObject],
    fibers: dict[ReportKey, frozenset[RepairObject]],
    orbit_by_object: dict[RepairObject, int],
) -> list[dict[str, object]]:
    rows = []
    for target_case in TARGET_ORDER:
        for shape in SHAPE_ORDER:
            members = [obj for obj in objects if obj.target_case == target_case and witness_shape(obj.witness) == shape]
            reports = {q_repair(obj.repair) for obj in members}
            shape_fibers = [
                key for key in fibers
                if key.target_case == target_case and key.shape == shape
            ]
            shape_orbits = {orbit_by_object[obj] for obj in members}
            rows.append(
                {
                    "target_case": target_case,
                    "shape": shape,
                    "witness_configuration_count": len({obj.witness for obj in members}),
                    "mcs_count": len(members),
                    "repair_object_count": len(members),
                    "report_count": len(reports),
                    "fiber_count": len(shape_fibers),
                    "orbit_count": len(shape_orbits),
                }
            )
    return rows


def shape_comparison_rows(
    *,
    fiber_rows: Sequence[dict[str, object]],
    orbit_rows: Sequence[dict[str, object]],
) -> tuple[list[dict[str, object]], dict[str, object]]:
    rows: list[dict[str, object]] = []
    distinct_by_target: dict[str, set[str]] = defaultdict(set)
    for target_case in TARGET_ORDER:
        for shape in SHAPE_ORDER:
            fibers = [
                row for row in fiber_rows
                if row["target_case"] == target_case and row["shape"] == shape
            ]
            orbits = [
                row for row in orbit_rows
                if row["target_case"] == target_case and row["shape"] == shape
            ]
            fibers_by_report = {
                str(row["report_label"]): int(row["fiber_size_mu"])
                for row in sorted(fibers, key=lambda row: report_sort_key(tuple(row["report"])))  # type: ignore[arg-type]
            }
            orbits_per_report = {
                str(row["report_label"]): int(row["number_of_orbits_in_fiber"])
                for row in sorted(fibers, key=lambda row: report_sort_key(tuple(row["report"])))  # type: ignore[arg-type]
            }
            partial_count = sum(1 for row in fibers if row["contains_partial_orbit_fragments"])
            signature = {
                "fiber_size_by_report": fibers_by_report,
                "orbit_size_multiset": sorted(int(row["orbit_size"]) for row in orbits),
                "number_of_orbits_per_report": orbits_per_report,
                "single_orbit_fiber_count": sum(1 for row in fibers if row["is_single_repair_orbit"]),
                "multi_orbit_fiber_count": sum(1 for row in fibers if not row["is_single_repair_orbit"]),
                "partial_orbit_fragment_count": partial_count,
                "stabilizer_size_multiset": sorted(int(row["stabilizer_size"]) for row in orbits),
                "report_labels_present": sorted(str(row["report_label"]) for row in fibers),
            }
            signature_key = json.dumps(signature, sort_keys=True)
            distinct_by_target[target_case].add(signature_key)
            rows.append(
                {
                    "target_case": target_case,
                    "shape": shape,
                    **signature,
                    "signature_key": signature_key,
                }
            )
    summary = {
        "distinct_signature_count_by_target": {
            target_case: len(distinct_by_target[target_case]) for target_case in TARGET_ORDER
        },
        "all_targets_have_o2_o3_o4_representative_level_differences": all(
            len(distinct_by_target[target_case]) == len(SHAPE_ORDER)
            for target_case in TARGET_ORDER
        ),
    }
    return rows, summary


def decide_verdict(
    *,
    phase1_validation: dict[str, object],
    well_definedness: dict[str, object],
    q_invariance: dict[str, object],
    fiber_rows: Sequence[dict[str, object]],
    orbit_rows: Sequence[dict[str, object]],
    orbit_stabilizer: dict[str, object],
    shape_summary: dict[str, object],
) -> tuple[str, list[str], str]:
    reasons = []
    if not phase1_validation["passes"]:
        reasons.append("Phase 1 expected counts or gate checks did not reproduce")
    if not well_definedness["passes"]:
        reasons.append("group action is not well-defined on semantic repair objects")
    if not q_invariance["passes"]:
        reasons.append("q is not invariant under S2 x S4")
    if not orbit_stabilizer["passes"]:
        reasons.append("orbit-stabilizer equation failed")
    partial_fibers = [row for row in fiber_rows if row["contains_partial_orbit_fragments"]]
    stable_union = all(bool(row["is_stable_union_of_complete_orbits"]) for row in fiber_rows)
    if partial_fibers:
        reasons.append("at least one report fiber contains partial orbit fragments")
    if not stable_union:
        reasons.append("not every report fiber decomposes into complete repair orbits")
    orbit_report_failures = [row for row in orbit_rows if not row["is_orbit_contained_in_one_report_fiber"]]
    if orbit_report_failures:
        reasons.append("at least one repair orbit crosses grouped-report fibers")
    if reasons:
        return "NO-GO", reasons, "Return to the warrant-contract track; do not implement warrant work in this task."

    shape_difference = bool(shape_summary["all_targets_have_o2_o3_o4_representative_level_differences"])
    every_fiber_single_orbit = all(bool(row["is_single_repair_orbit"]) for row in fiber_rows)
    if shape_difference and every_fiber_single_orbit:
        return (
            "STRONG GO TO PHASE 3 DESIGN",
            [
                "the action is well-defined, q is invariant, every shape-indexed report fiber is a single repair orbit, and O2/O3/O4 signatures differ at representative level",
            ],
            "Write a theoretical design document for Obstruction-Indexed Repair-Orbit Classification before any theorem implementation.",
        )
    if shape_difference and stable_union:
        return (
            "STRONG GO TO PHASE 3 DESIGN",
            [
                "the action is well-defined, q is invariant, fibers are stable finite unions of complete orbits, and O2/O3/O4 signatures differ at representative level",
            ],
            "Write a theoretical design document for Grouped Report Partial-Identification before any theorem implementation.",
        )
    if stable_union:
        return (
            "CONDITIONAL GO",
            [
                "the action and grouped reports are coherent, but some O2/O3/O4 orbit/fiber signatures coincide",
            ],
            "Write a theoretical design document with explicit case distinctions; do not run 3-voter analysis yet.",
        )
    return (
        "WEAK GO / NEEDS 3-VOTER",
        [
            "the two-voter structure is coherent but does not yet show enough obstruction-indexed dependence",
        ],
        "Design a 3-voter semantic S3 extension precheck, but do not run it yet.",
    )


def analyze_phase1_payload(
    phase1_payload: dict[str, object],
    phase1_source: dict[str, object] | None = None,
) -> dict[str, object]:
    phase1_validation = validate_phase1_payload(phase1_payload)
    objects, family = repair_objects_from_phase1(phase1_payload)
    group = group_elements()
    if len(group) != 48:
        raise AssertionError(f"expected |S2 x S4| = 48, got {len(group)}")

    well_definedness = check_well_definedness(objects=objects, family=family, group=group)
    q_invariance = check_q_invariance(objects=objects, group=group)
    orbit_rows, orbit_by_object, orbit_sets = compute_orbits(objects=objects, group=group)
    orbit_stabilizer = check_orbit_stabilizer_equation(objects=objects, group=group)
    fibers = build_fibers(objects)
    fiber_rows = analyze_fibers(
        fibers=fibers,
        orbit_by_object=orbit_by_object,
        orbit_sets=orbit_sets,
        orbit_rows=orbit_rows,
    )
    count_rows = object_counts(objects=objects, fibers=fibers, orbit_by_object=orbit_by_object)
    shape_rows, shape_summary = shape_comparison_rows(fiber_rows=fiber_rows, orbit_rows=orbit_rows)
    verdict, reasons, next_action = decide_verdict(
        phase1_validation=phase1_validation,
        well_definedness=well_definedness,
        q_invariance=q_invariance,
        fiber_rows=fiber_rows,
        orbit_rows=orbit_rows,
        orbit_stabilizer=orbit_stabilizer,
        shape_summary=shape_summary,
    )

    return {
        "schema_version": 1,
        "phase": "M4 Phase 2 two-voter repair-orbit and grouped-report precheck",
        "phase1_source": phase1_source or {"mode": "in-memory"},
        "phase1_validation": phase1_validation,
        "repair_object_definition": {
            "name": "RepairObject",
            "fields": ["target_case", "W", "R"],
            "W": "((voter0, P), (voter1, Q)) with unordered alternative pairs P,Q",
            "R": "semantic MCS for the selector-free fixed-witness theory associated with W",
            "rights_atom_schema": "right(voter, unordered_alt_pair)",
            "base_atoms": list(smp.BASE_ORDER),
        },
        "group": {
            "name": "S2_voters x S4_alternatives",
            "size": len(group),
            "voter_elements": ["id", "tau"],
            "alternative_element_count": 24,
            "target_case_fixed": True,
            "elements": [group_element_label(element) for element in group],
        },
        "grouped_report_map": {
            "q_atom": {
                "asymm": "asymm",
                "un": "un",
                "no_cycle3": "no_cycle3",
                "no_cycle4": "no_cycle4",
                "right(voter,P)": "minlib",
            },
            "q_repair": "sorted set { q_atom(a) | a in R }",
            "q_object": "(target_case, overlap_class(W), q(R))",
            "primary_fibers_fix_shape": True,
        },
        "formal_mu": {
            "definition": "mu(target_case, shape, report) = |Fiber(target_case, shape, report)|",
            "distinguished_from_phase1": "Phase 1 did not define formal report-fiber multiplicity.",
        },
        "repair_object_count": len(objects),
        "report_fiber_count": len(fibers),
        "repair_orbit_count": len(orbit_rows),
        "object_counts": count_rows,
        "well_definedness": well_definedness,
        "q_invariance": q_invariance,
        "orbit_stabilizer": orbit_stabilizer,
        "report_fibers": fiber_rows,
        "repair_orbits": orbit_rows,
        "shape_comparison": {
            "rows": shape_rows,
            "summary": shape_summary,
        },
        "verdict": verdict,
        "verdict_reasons": reasons,
        "next_authorized_action": next_action,
        "non_claims": NON_CLAIMS,
    }


def _csv_value(value: object) -> object:
    if isinstance(value, (dict, list, tuple)):
        return json.dumps(value, sort_keys=True)
    return value


def write_csv(path: Path, rows: Sequence[dict[str, object]]) -> None:
    if not rows:
        return
    with path.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=list(rows[0].keys()))
        writer.writeheader()
        for row in rows:
            writer.writerow({key: _csv_value(value) for key, value in row.items()})


def write_outputs(out_dir: Path, payload: dict[str, object]) -> None:
    out_dir.mkdir(parents=True, exist_ok=True)
    (out_dir / "repair_orbit_precheck_results.json").write_text(
        json.dumps(payload, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    write_csv(out_dir / "object_counts.csv", payload["object_counts"])  # type: ignore[arg-type]
    write_csv(out_dir / "report_fibers.csv", payload["report_fibers"])  # type: ignore[arg-type]
    write_csv(out_dir / "repair_orbits.csv", payload["repair_orbits"])  # type: ignore[arg-type]
    write_csv(out_dir / "shape_comparison.csv", payload["shape_comparison"]["rows"])  # type: ignore[index,arg-type]


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--out-dir", type=Path, default=OUT_DEFAULT)
    parser.add_argument("--phase1-json", type=Path, default=PHASE1_JSON_DEFAULT)
    parser.add_argument("--phase1-out-dir", type=Path, default=PHASE1_OUT_DEFAULT)
    parser.add_argument("--solver", default="cadical")
    parser.add_argument("--timeout", type=float, default=20.0)
    parser.add_argument("--force-regenerate-phase1", action="store_true")
    args = parser.parse_args()

    phase1_payload, phase1_source = load_phase1_payload(
        phase1_json=args.phase1_json,
        phase1_out_dir=args.phase1_out_dir,
        solver=args.solver,
        timeout=args.timeout,
        force_regenerate=args.force_regenerate_phase1,
    )
    payload = analyze_phase1_payload(phase1_payload, phase1_source=phase1_source)
    payload["out_dir"] = str(args.out_dir)
    write_outputs(args.out_dir, payload)
    print(
        json.dumps(
            {
                "out_dir": str(args.out_dir),
                "phase1_source_mode": phase1_source["mode"],
                "repair_object_count": payload["repair_object_count"],
                "report_fiber_count": payload["report_fiber_count"],
                "repair_orbit_count": payload["repair_orbit_count"],
                "group_size": payload["group"]["size"],  # type: ignore[index]
                "well_definedness": payload["well_definedness"]["passes"],  # type: ignore[index]
                "q_invariance": payload["q_invariance"]["passes"],  # type: ignore[index]
                "verdict": payload["verdict"],
            },
            indent=2,
            sort_keys=True,
        )
    )


if __name__ == "__main__":
    main()
