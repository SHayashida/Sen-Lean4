#!/usr/bin/env python3
"""Selector-free semantic MUS/MCS precheck for the pre-M4 gate.

This script is exploratory and intentionally isolated under
``scripts/exploration/m4``. It does not modify production encoders and does not
reuse the Sen24 ``minlib`` selector implementation as a MUS unit.
"""

from __future__ import annotations

import argparse
import csv
import itertools
import json
import platform
import shutil
import subprocess
import sys
import tempfile
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable

REPO_ROOT = Path(__file__).resolve().parents[3]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from encoding.axioms import AXIOM_REGISTRY  # noqa: E402
from encoding.schema import FiniteSchema  # noqa: E402

ALT_VALUES = (0, 1, 2, 3)
VOTERS = (0, 1)
BASE_ORDER = ("asymm", "un", "no_cycle3", "no_cycle4")
PAIR_ORDER = tuple(itertools.combinations(ALT_VALUES, 2))
OUT_DEFAULT = Path("/tmp/sen_m4_semantic_mus")


@dataclass(frozen=True)
class TargetResidual:
    case_id: str
    production_levers: tuple[str, ...]
    base_atoms: tuple[str, ...]


TARGET_RESIDUALS = (
    TargetResidual(
        case_id="case_11101",
        production_levers=("asymm", "un", "minlib", "no_cycle4"),
        base_atoms=("asymm", "un", "no_cycle4"),
    ),
    TargetResidual(
        case_id="case_11111",
        production_levers=("asymm", "un", "minlib", "no_cycle3", "no_cycle4"),
        base_atoms=("asymm", "un", "no_cycle3", "no_cycle4"),
    ),
)


def canonical_pair(a: int, b: int) -> tuple[int, int]:
    if a == b:
        raise ValueError("an unordered alternative pair needs distinct endpoints")
    if a not in ALT_VALUES or b not in ALT_VALUES:
        raise ValueError(f"alternative out of Sen24 range: {(a, b)}")
    return (a, b) if a < b else (b, a)


def pair_code(pair: tuple[int, int]) -> str:
    a, b = canonical_pair(*pair)
    return f"{a}{b}"


def right_atom(voter: int, pair: tuple[int, int]) -> str:
    if voter not in VOTERS:
        raise ValueError(f"unknown voter {voter}")
    a, b = canonical_pair(*pair)
    return f"right:v{voter}:{a}-{b}"


def is_right_atom(atom: str) -> bool:
    return atom.startswith("right:v")


def parse_right_atom(atom: str) -> tuple[int, tuple[int, int]]:
    try:
        prefix, pair_raw = atom.split(":", 2)[1:]
        voter = int(prefix.removeprefix("v"))
        a_raw, b_raw = pair_raw.split("-", 1)
        return voter, canonical_pair(int(a_raw), int(b_raw))
    except Exception as exc:  # pragma: no cover - error path is defensive
        raise ValueError(f"not a right atom: {atom!r}") from exc


def atom_label(atom: str) -> str:
    if not is_right_atom(atom):
        return atom
    voter, pair = parse_right_atom(atom)
    return f"right(voter{voter},{{{pair[0]},{pair[1]}}})"


def atom_sort_key(atom: str) -> tuple[int, int, int, str]:
    if atom in BASE_ORDER:
        return (0, BASE_ORDER.index(atom), -1, atom)
    if not is_right_atom(atom):
        return (2, 0, 0, atom)
    voter, pair = parse_right_atom(atom)
    return (1, voter, PAIR_ORDER.index(pair), atom)


def sorted_atoms(atoms: Iterable[str]) -> tuple[str, ...]:
    return tuple(sorted(set(atoms), key=atom_sort_key))


def voter_swap_atom(atom: str) -> str:
    if not is_right_atom(atom):
        return atom
    voter, pair = parse_right_atom(atom)
    return right_atom(1 - voter, pair)


def alt_permute_atom(atom: str, perm: tuple[int, int, int, int]) -> str:
    if not is_right_atom(atom):
        return atom
    voter, pair = parse_right_atom(atom)
    return right_atom(voter, canonical_pair(perm[pair[0]], perm[pair[1]]))


def alt_permute_pair(pair: tuple[int, int], perm: tuple[int, int, int, int]) -> tuple[int, int]:
    return canonical_pair(perm[pair[0]], perm[pair[1]])


def config_id(pair0: tuple[int, int], pair1: tuple[int, int]) -> str:
    return f"v0_{pair_code(pair0)}__v1_{pair_code(pair1)}"


def alt_canonical_config_id(pair0: tuple[int, int], pair1: tuple[int, int]) -> str:
    return min(
        config_id(alt_permute_pair(pair0, perm), alt_permute_pair(pair1, perm))
        for perm in itertools.permutations(ALT_VALUES)
    )


def swap_config_id(config: str) -> str:
    pair0, pair1 = parse_config_id(config)
    return config_id(pair1, pair0)


def parse_config_id(config: str) -> tuple[tuple[int, int], tuple[int, int]]:
    left, right = config.split("__")
    left_pair = left.removeprefix("v0_")
    right_pair = right.removeprefix("v1_")
    return (
        canonical_pair(int(left_pair[0]), int(left_pair[1])),
        canonical_pair(int(right_pair[0]), int(right_pair[1])),
    )


def overlap_class(pair0: tuple[int, int], pair1: tuple[int, int]) -> str:
    overlap = len(set(pair0).intersection(pair1))
    if overlap == 2:
        return "O2"
    if overlap == 1:
        return "O3"
    if overlap == 0:
        return "O4"
    raise AssertionError("unreachable pair-overlap size")


def witness_configs() -> list[tuple[tuple[int, int], tuple[int, int]]]:
    return [(p0, p1) for p0 in PAIR_ORDER for p1 in PAIR_ORDER]


def _right_clauses(schema: FiniteSchema, voter: int, pair: tuple[int, int]) -> list[list[int]]:
    a, b = canonical_pair(*pair)
    clauses: list[list[int]] = []
    for profile in range(schema.n_profiles):
        lit = schema.var_p(profile, a, b) if schema.prefers(profile, voter, a, b) else schema.var_p(profile, b, a)
        clauses.append([lit])
    return clauses


def atom_clauses(schema: FiniteSchema, atom: str) -> list[list[int]]:
    if atom in BASE_ORDER:
        clauses: list[list[int]] = []
        AXIOM_REGISTRY[atom].encode(schema, clauses)
        return clauses
    voter, pair = parse_right_atom(atom)
    return _right_clauses(schema, voter, pair)


def guarded_subset_clauses(
    *,
    atom_blocks: dict[str, list[list[int]]],
    guard_vars: dict[str, int],
    selected_atoms: Iterable[str],
) -> list[list[int]]:
    clauses: list[list[int]] = []
    for atom in sorted_atoms(selected_atoms):
        guard = guard_vars[atom]
        clauses.append([guard])
        for clause in atom_blocks[atom]:
            clauses.append([-guard, *clause])
    return clauses


def write_dimacs(path: Path, nvars: int, clauses: list[list[int]]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", encoding="utf-8") as handle:
        handle.write(f"p cnf {nvars} {len(clauses)}\n")
        for clause in clauses:
            handle.write(" ".join(str(lit) for lit in clause) + " 0\n")


def solver_status(solver: str, cnf_path: Path, timeout: float) -> tuple[str, int, str]:
    try:
        proc = subprocess.run(
            [solver, str(cnf_path)],
            capture_output=True,
            text=True,
            check=False,
            timeout=timeout,
        )
    except subprocess.TimeoutExpired as exc:
        return "UNKNOWN", -1, f"timeout after {timeout}s: {exc}"
    text = f"{proc.stdout}\n{proc.stderr}"
    if proc.returncode == 10 or "SATISFIABLE" in text.upper() and "UNSATISFIABLE" not in text.upper():
        return "SAT", proc.returncode, text
    if proc.returncode == 20 or "UNSATISFIABLE" in text.upper():
        return "UNSAT", proc.returncode, text
    return "UNKNOWN", proc.returncode, text


def powerset(atoms: tuple[str, ...]) -> list[tuple[str, ...]]:
    subsets: list[tuple[str, ...]] = []
    for size in range(len(atoms) + 1):
        subsets.extend(itertools.combinations(atoms, size))
    return [tuple(s) for s in subsets]


def is_subset(a: Iterable[str], b: Iterable[str]) -> bool:
    return set(a).issubset(set(b))


def minimal_sets(candidates: Iterable[Iterable[str]]) -> list[tuple[str, ...]]:
    unique = [sorted_atoms(c) for c in {frozenset(c) for c in candidates}]
    mins: list[tuple[str, ...]] = []
    for cand in unique:
        cand_set = set(cand)
        if not any(set(other) < cand_set for other in unique):
            mins.append(cand)
    return sorted(mins, key=lambda s: (len(s), [atom_sort_key(a) for a in s]))


def compute_mus(status_by_subset: dict[frozenset[str], str]) -> list[tuple[str, ...]]:
    return minimal_sets(subset for subset, status in status_by_subset.items() if status == "UNSAT")


def compute_mcs(universe: tuple[str, ...], status_by_subset: dict[frozenset[str], str]) -> list[tuple[str, ...]]:
    full = set(universe)
    correction_sets = []
    for retained, status in status_by_subset.items():
        if status == "SAT":
            correction_sets.append(full.difference(retained))
    return minimal_sets(correction_sets)


def hits_all(candidate: Iterable[str], hyperedges: Iterable[Iterable[str]]) -> bool:
    candidate_set = set(candidate)
    return all(candidate_set.intersection(edge) for edge in hyperedges)


def minimal_hitting_sets(
    universe: tuple[str, ...],
    hyperedges: list[tuple[str, ...]],
) -> list[tuple[str, ...]]:
    if not hyperedges:
        return []
    hits = []
    for subset in powerset(universe):
        if hits_all(subset, hyperedges):
            hits.append(subset)
    return minimal_sets(hits)


def transform_family(
    family: list[tuple[str, ...]],
    transform,
) -> list[tuple[str, ...]]:
    return sorted(
        (sorted_atoms(transform(atom) for atom in member) for member in family),
        key=lambda s: (len(s), [atom_sort_key(a) for a in s]),
    )


def family_key(family: list[tuple[str, ...]]) -> tuple[tuple[str, ...], ...]:
    return tuple(sorted(family, key=lambda s: (len(s), [atom_sort_key(a) for a in s])))


def alt_canonical_family(family: list[tuple[str, ...]]) -> tuple[tuple[str, ...], ...]:
    keys = []
    for perm in itertools.permutations(ALT_VALUES):
        transformed = transform_family(family, lambda atom, p=perm: alt_permute_atom(atom, p))
        keys.append(family_key(transformed))
    return min(keys)


def solver_metadata(solver: str) -> dict[str, object]:
    path = shutil.which(solver)
    version_raw = "unknown"
    try:
        proc = subprocess.run([solver, "--version"], capture_output=True, text=True, timeout=5)
        version_raw = "\n".join(x for x in [proc.stdout.strip(), proc.stderr.strip()] if x).strip() or "unknown"
    except Exception:
        pass
    return {
        "solver": solver,
        "solver_path": str(Path(path).resolve()) if path else "not found",
        "solver_version_raw": version_raw,
        "python_version": sys.version.split()[0],
        "platform": platform.platform(),
    }


def analyze_rights(mus: list[tuple[str, ...]], rights_atoms: tuple[str, ...]) -> dict[str, object]:
    rights_set = set(rights_atoms)
    supports = [sorted_atoms(set(edge).intersection(rights_set)) for edge in mus]
    if supports:
        intersection = set(supports[0])
        for support in supports[1:]:
            intersection.intersection_update(support)
    else:
        intersection = set()
    rights_only_hs = minimal_hitting_sets(rights_atoms, mus)
    only_one_voter = False
    only_one_voter_id: int | None = None
    if len(intersection) == 1:
        only_one_voter = True
        only_one_voter_id = parse_right_atom(next(iter(intersection)))[0]
    return {
        "rights_support_by_mus": [[atom_label(a) for a in support] for support in supports],
        "rights_intersection": [atom_label(a) for a in sorted_atoms(intersection)],
        "minimal_rights_only_hitting_sets": [
            [atom_label(a) for a in member] for member in rights_only_hs
        ],
        "any_mus_contains_neither_right": any(len(support) == 0 for support in supports),
        "every_mus_contains_both_rights": bool(supports) and all(len(support) == len(rights_atoms) for support in supports),
        "only_one_voters_right_present_in_every_mus": only_one_voter,
        "only_one_voter_id": only_one_voter_id,
    }


def mcs_voter_multiplicity(mcs: list[tuple[str, ...]]) -> dict[str, object]:
    singleton_rights = []
    voter_counts = {0: 0, 1: 0}
    rights_participation = {0: 0, 1: 0}
    for deletion in mcs:
        rights = [a for a in deletion if is_right_atom(a)]
        voters = sorted({parse_right_atom(a)[0] for a in rights})
        for voter in voters:
            rights_participation[voter] += 1
        if len(deletion) == 1 and rights:
            atom = rights[0]
            voter = parse_right_atom(atom)[0]
            voter_counts[voter] += 1
            singleton_rights.append(atom)
    return {
        "singleton_right_mcs": [atom_label(a) for a in sorted_atoms(singleton_rights)],
        "singleton_right_mcs_by_voter": {f"voter{v}": voter_counts[v] for v in VOTERS},
        "mcs_with_right_by_voter": {f"voter{v}": rights_participation[v] for v in VOTERS},
        "semantic_voter_indexed_repair_multiplicity_survives": all(voter_counts[v] > 0 for v in VOTERS),
    }


def normalize_atom_for_shape(atom: str, rights_atoms: tuple[str, str]) -> str:
    if atom == rights_atoms[0]:
        return "R0"
    if atom == rights_atoms[1]:
        return "R1"
    return atom


def normalize_family_for_shape(
    family: list[tuple[str, ...]],
    rights_atoms: tuple[str, str],
) -> tuple[tuple[str, ...], ...]:
    normalized = []
    for edge in family:
        normalized.append(tuple(sorted(normalize_atom_for_shape(atom, rights_atoms) for atom in edge)))
    return tuple(sorted(normalized, key=lambda edge: (len(edge), list(edge))))


def multiset(values: Iterable[object]) -> list[object]:
    return sorted(values)


def hypergraph_degree_sequence(
    family: list[tuple[str, ...]],
    rights_atoms: tuple[str, str],
) -> list[tuple[str, int]]:
    degree: dict[str, int] = {}
    for edge in family:
        for atom in edge:
            key = normalize_atom_for_shape(atom, rights_atoms)
            degree[key] = degree.get(key, 0) + 1
    return sorted(degree.items(), key=lambda item: (item[1], item[0]))


def shape_signature(
    *,
    mus: list[tuple[str, ...]],
    mcs: list[tuple[str, ...]],
    rights_atoms: tuple[str, str],
    swap_row: dict[str, object] | None,
) -> dict[str, object]:
    rights_support = []
    rights_set = set(rights_atoms)
    for edge in mus:
        support = tuple(sorted(normalize_atom_for_shape(atom, rights_atoms) for atom in set(edge) & rights_set))
        rights_support.append(support)
    rights_intersection = set(rights_atoms)
    for edge in mus:
        rights_intersection.intersection_update(set(edge))
    rights_only_hs = minimal_hitting_sets(rights_atoms, mus)
    provisional_mu_family = normalize_family_for_shape(rights_only_hs, rights_atoms)
    return {
        "mus_count_per_representative": len(mus),
        "mus_cardinality_multiset": multiset(len(edge) for edge in mus),
        "mcs_count_per_representative": len(mcs),
        "mcs_cardinality_multiset": multiset(len(edge) for edge in mcs),
        "provisional_voter_indexed_semantic_repair_multiplicity": len(provisional_mu_family),
        "mu_note": "Phase 1 records voter-indexed semantic repair multiplicity, not formal report-fiber mu.",
        "rights_participation_multiset": [list(edge) for edge in sorted(rights_support)],
        "rights_core_intersection": sorted(normalize_atom_for_shape(atom, rights_atoms) for atom in rights_intersection),
        "minimal_rights_only_hitting_set_family": [list(edge) for edge in provisional_mu_family],
        "mus_hypergraph_degree_sequence": [[atom, degree] for atom, degree in hypergraph_degree_sequence(mus, rights_atoms)],
        "voter_swap_stabilizer_profile": {
            "full_stabilizer": swap_row["full_stabilizer"] if swap_row is not None else "computed after swap pass",
            "proper_stabilizer": swap_row["proper_stabilizer"] if swap_row is not None else "computed after swap pass",
        },
        "repair_orbit_size_profile": {
            "orbit_size": swap_row["orbit_size"] if swap_row is not None else "computed after swap pass",
        },
    }


def structural_signature_key(signature: dict[str, object]) -> str:
    """Key excluding aggregate counts, voter-swap stabilizer, and orbit size."""
    structural = {
        "mus_cardinality_multiset": signature["mus_cardinality_multiset"],
        "mcs_cardinality_multiset": signature["mcs_cardinality_multiset"],
        "rights_participation_multiset": signature["rights_participation_multiset"],
        "rights_core_intersection": signature["rights_core_intersection"],
        "minimal_rights_only_hitting_set_family": signature["minimal_rights_only_hitting_set_family"],
        "mus_hypergraph_degree_sequence": signature["mus_hypergraph_degree_sequence"],
        "provisional_voter_indexed_semantic_repair_multiplicity": signature[
            "provisional_voter_indexed_semantic_repair_multiplicity"
        ],
    }
    return json.dumps(structural, sort_keys=True)


def run_configuration(
    *,
    target: TargetResidual,
    pair0: tuple[int, int],
    pair1: tuple[int, int],
    solver: str,
    timeout: float,
    work_dir: Path,
) -> dict[str, object]:
    schema = FiniteSchema(n=2, m=4, minlib_mode="disabled")
    rights_atoms = (right_atom(0, pair0), right_atom(1, pair1))
    universe = sorted_atoms((*target.base_atoms, *rights_atoms))
    guard_vars = {atom: schema.n_p_vars + idx + 1 for idx, atom in enumerate(universe)}
    atom_blocks = {atom: atom_clauses(schema, atom) for atom in universe}
    nvars = schema.n_p_vars + len(universe)
    status_by_subset: dict[frozenset[str], str] = {}
    subset_rows = []
    unknown_subsets = []
    case_work = work_dir / target.case_id / config_id(pair0, pair1)
    case_work.mkdir(parents=True, exist_ok=True)

    with tempfile.TemporaryDirectory(prefix="cnf_", dir=str(case_work)) as tmp_raw:
        tmp_dir = Path(tmp_raw)
        for subset in powerset(universe):
            selected = sorted_atoms(subset)
            clauses = guarded_subset_clauses(
                atom_blocks=atom_blocks,
                guard_vars=guard_vars,
                selected_atoms=selected,
            )
            cnf_path = tmp_dir / "subset.cnf"
            write_dimacs(cnf_path, nvars, clauses)
            status, return_code, _solver_output = solver_status(solver, cnf_path, timeout)
            status_by_subset[frozenset(selected)] = status
            if status == "UNKNOWN":
                unknown_subsets.append(selected)
            subset_rows.append(
                {
                    "target_case": target.case_id,
                    "config_id": config_id(pair0, pair1),
                    "overlap_class": overlap_class(pair0, pair1),
                    "retained_atoms": [atom_label(a) for a in selected],
                    "retained_atom_ids": list(selected),
                    "status": status,
                    "solver_return_code": return_code,
                }
            )

    mus = compute_mus(status_by_subset)
    mcs = compute_mcs(universe, status_by_subset)
    hitting_sets = minimal_hitting_sets(universe, mus)
    duality_passes = family_key(mcs) == family_key(hitting_sets)
    full_status = status_by_subset[frozenset(universe)]
    rights_analysis = analyze_rights(mus, rights_atoms)
    multiplicity = mcs_voter_multiplicity(mcs)
    preliminary_signature = shape_signature(
        mus=mus,
        mcs=mcs,
        rights_atoms=rights_atoms,
        swap_row=None,
    )
    labels = {atom: atom_label(atom) for atom in universe}
    return {
        "target_case": target.case_id,
        "production_levers": list(target.production_levers),
        "base_atoms": list(target.base_atoms),
        "config_id": config_id(pair0, pair1),
        "alternative_relabeling_canonical_representative": alt_canonical_config_id(pair0, pair1),
        "pair_voter0": list(pair0),
        "pair_voter1": list(pair1),
        "overlap_class": overlap_class(pair0, pair1),
        "active_semantic_atoms": [labels[a] for a in universe],
        "active_semantic_atom_ids": list(universe),
        "right_atoms": [labels[a] for a in rights_atoms],
        "right_atom_ids": list(rights_atoms),
        "guard_variables": {labels[a]: guard_vars[a] for a in universe},
        "guard_variable_ids": guard_vars,
        "clause_provenance_counts": {labels[a]: len(atom_blocks[a]) for a in universe},
        "clause_provenance_count_ids": {a: len(atom_blocks[a]) for a in universe},
        "subset_count": len(status_by_subset),
        "status_counts": {
            status: sum(1 for value in status_by_subset.values() if value == status)
            for status in ("SAT", "UNSAT", "UNKNOWN")
        },
        "full_package_status": full_status,
        "unknown_subsets": [[labels[a] for a in subset] for subset in unknown_subsets],
        "unknown_subset_count": len(unknown_subsets),
        "mus": [[labels[a] for a in edge] for edge in mus],
        "mus_ids": [list(edge) for edge in mus],
        "mcs": [[labels[a] for a in deletion] for deletion in mcs],
        "mcs_ids": [list(deletion) for deletion in mcs],
        "minimal_hitting_sets_from_mus": [[labels[a] for a in hs] for hs in hitting_sets],
        "minimal_hitting_set_ids_from_mus": [list(hs) for hs in hitting_sets],
        "mus_count": len(mus),
        "mcs_count": len(mcs),
        "duality_passes": duality_passes,
        "rights_analysis": rights_analysis,
        "mcs_voter_index_multiplicity": multiplicity,
        "shape_signature_pre_swap": preliminary_signature,
        "selector_free": True,
        "selector_contamination_excluded": True,
        "subset_rows": subset_rows,
    }


def evaluate_voter_swap(results: dict[tuple[str, str], dict[str, object]]) -> tuple[bool, list[dict[str, object]]]:
    rows = []
    all_pass = True
    for (target_case, cfg), result in sorted(results.items()):
        swapped_cfg = swap_config_id(cfg)
        other = results[(target_case, swapped_cfg)]
        mus = [tuple(edge) for edge in result["mus_ids"]]  # type: ignore[index]
        mcs = [tuple(edge) for edge in result["mcs_ids"]]  # type: ignore[index]
        swapped_mus = transform_family(mus, voter_swap_atom)
        swapped_mcs = transform_family(mcs, voter_swap_atom)
        other_mus = [tuple(edge) for edge in other["mus_ids"]]  # type: ignore[index]
        other_mcs = [tuple(edge) for edge in other["mcs_ids"]]  # type: ignore[index]
        mus_pass = family_key(swapped_mus) == family_key(other_mus)
        mcs_pass = family_key(swapped_mcs) == family_key(other_mcs)
        if not (mus_pass and mcs_pass):
            all_pass = False
        orbit_size = 1 if swapped_cfg == cfg else 2
        stabilizer = ["id"]
        if swapped_cfg == cfg and mus_pass and mcs_pass:
            stabilizer.append("tau")
        rows.append(
            {
                "target_case": target_case,
                "config_id": cfg,
                "tau_config_id": swapped_cfg,
                "mus_equivariant": mus_pass,
                "mcs_equivariant": mcs_pass,
                "full_stabilizer": stabilizer,
                "proper_stabilizer": [g for g in stabilizer if g != "id"],
                "orbit_size": orbit_size,
            }
        )
    return all_pass, rows


def evaluate_alt_relabeling(results: dict[tuple[str, str], dict[str, object]]) -> tuple[bool, list[dict[str, object]]]:
    rows = []
    all_pass = True
    for target in TARGET_RESIDUALS:
        for cls in ("O2", "O3", "O4"):
            members = [
                result
                for (target_case, _cfg), result in results.items()
                if target_case == target.case_id and result["overlap_class"] == cls
            ]
            mus_forms = {
                alt_canonical_family([tuple(edge) for edge in result["mus_ids"]])  # type: ignore[index]
                for result in members
            }
            mcs_forms = {
                alt_canonical_family([tuple(edge) for edge in result["mcs_ids"]])  # type: ignore[index]
                for result in members
            }
            signature_forms = {
                json.dumps(result["shape_signature_pre_swap"], sort_keys=True)
                for result in members
            }
            representatives = sorted(
                {str(result["alternative_relabeling_canonical_representative"]) for result in members}
            )
            passed = len(mus_forms) == 1 and len(mcs_forms) == 1 and len(signature_forms) == 1 and len(representatives) == 1
            if not passed:
                all_pass = False
            rows.append(
                {
                    "target_case": target.case_id,
                    "overlap_class": cls,
                    "configuration_count": len(members),
                    "canonical_representatives": representatives,
                    "mus_alt_canonical_forms": len(mus_forms),
                    "mcs_alt_canonical_forms": len(mcs_forms),
                    "shape_signature_forms": len(signature_forms),
                    "alternative_relabeling_uniform": passed,
                }
            )
    return all_pass, rows


def attach_shape_signatures(
    config_results: list[dict[str, object]],
    swap_rows: list[dict[str, object]],
) -> list[dict[str, object]]:
    swap_by_key = {(str(row["target_case"]), str(row["config_id"])): row for row in swap_rows}
    for result in config_results:
        mus = [tuple(edge) for edge in result["mus_ids"]]  # type: ignore[index]
        mcs = [tuple(edge) for edge in result["mcs_ids"]]  # type: ignore[index]
        rights_atoms = tuple(result["right_atom_ids"])  # type: ignore[arg-type]
        if len(rights_atoms) != 2:
            raise ValueError(f"expected exactly two rights atoms: {rights_atoms!r}")
        swap_row = swap_by_key[(str(result["target_case"]), str(result["config_id"]))]
        result["shape_signature"] = shape_signature(
            mus=mus,
            mcs=mcs,
            rights_atoms=(str(rights_atoms[0]), str(rights_atoms[1])),
            swap_row=swap_row,
        )
    return config_results


def build_shape_comparison(config_results: list[dict[str, object]]) -> dict[str, object]:
    rows: list[dict[str, object]] = []
    by_target: dict[str, dict[str, dict[str, object]]] = {}
    for target in TARGET_RESIDUALS:
        by_target[target.case_id] = {}
        for cls in ("O2", "O3", "O4"):
            members = [
                result for result in config_results
                if result["target_case"] == target.case_id and result["overlap_class"] == cls
            ]
            signature_keys = {json.dumps(result["shape_signature"], sort_keys=True) for result in members}
            structural_keys = {structural_signature_key(result["shape_signature"]) for result in members}  # type: ignore[arg-type]
            representatives = sorted(
                {str(result["alternative_relabeling_canonical_representative"]) for result in members}
            )
            representative = next(result for result in members if result["config_id"] == representatives[0])
            row = {
                "target_case": target.case_id,
                "overlap_class": cls,
                "configuration_count": len(members),
                "canonical_representative": representatives[0],
                "representative_signature_stable": len(signature_keys) == 1 and len(structural_keys) == 1,
                "signature_form_count": len(signature_keys),
                "structural_signature_form_count": len(structural_keys),
                "shape_signature": representative["shape_signature"],
            }
            rows.append(row)
            by_target[target.case_id][cls] = row

    target_summaries: list[dict[str, object]] = []
    all_targets_have_structural_difference = True
    all_shapes_stable = all(bool(row["representative_signature_stable"]) for row in rows)
    for target in TARGET_RESIDUALS:
        structural_keys = {
            structural_signature_key(by_target[target.case_id][cls]["shape_signature"])  # type: ignore[arg-type]
            for cls in ("O2", "O3", "O4")
        }
        has_difference = len(structural_keys) > 1
        all_targets_have_structural_difference = all_targets_have_structural_difference and has_difference
        target_summaries.append(
            {
                "target_case": target.case_id,
                "shape_signature_distinct_structural_forms": len(structural_keys),
                "has_shape_structural_difference": has_difference,
                "difference_is_not_aggregate_count_only": has_difference,
                "difference_is_not_selector_machinery": True,
                "difference_is_not_voter_swap_only": has_difference,
            }
        )
    return {
        "rows": rows,
        "target_summaries": target_summaries,
        "all_representative_signatures_stable": all_shapes_stable,
        "all_targets_have_shape_structural_difference": all_targets_have_structural_difference,
    }


def decide_gate(
    config_results: list[dict[str, object]],
    swap_pass: bool,
    alt_pass: bool,
    shape_comparison: dict[str, object],
) -> tuple[str, list[str]]:
    reasons = []
    unknown = any(int(r["unknown_subset_count"]) > 0 for r in config_results)
    full_unsat = all(r["full_package_status"] == "UNSAT" for r in config_results)
    rights_free_mus = any(r["rights_analysis"]["any_mus_contains_neither_right"] for r in config_results)  # type: ignore[index]
    duality = all(bool(r["duality_passes"]) for r in config_results)
    multiplicity = all(
        bool(r["mcs_voter_index_multiplicity"]["semantic_voter_indexed_repair_multiplicity_survives"])  # type: ignore[index]
        for r in config_results
    )
    selector_free = all(bool(r["selector_contamination_excluded"]) for r in config_results)
    if unknown:
        reasons.append("UNKNOWN subset status prevents complete classification")
    if not full_unsat:
        reasons.append("at least one selector-free full package is not UNSAT")
    if rights_free_mus:
        reasons.append("at least one MUS contains neither right")
    if not duality:
        reasons.append("MUS/MCS duality failed")
    if not swap_pass:
        reasons.append("voter-swap equivariance failed")
    if not multiplicity:
        reasons.append("semantic voter-indexed repair multiplicity disappeared")
    if not selector_free:
        reasons.append("selector contamination was not excluded")
    if reasons:
        return "NO-GO", reasons
    stable = bool(shape_comparison["all_representative_signatures_stable"])
    shape_difference = bool(shape_comparison["all_targets_have_shape_structural_difference"])
    if alt_pass and stable and shape_difference:
        return "STRONG GO", [
            "selector-free semantic multiplicity, duality, equivariance, within-shape stability, and cross-shape structural dependence all passed"
        ]
    if not stable:
        return "WEAK GO / CONDITIONAL GO", [
            "semantic multiplicity and equivariance survive, but representative signatures are not stable within O2/O3/O4 classes"
        ]
    if not shape_difference:
        return "WEAK GO / CONDITIONAL GO", [
            "semantic multiplicity and equivariance survive, but pre-registered ShapeSignature components do not distinguish O2/O3/O4"
        ]
    return "WEAK GO / CONDITIONAL GO", [
        "semantic multiplicity and equivariance survive, but alternative-relabeling checks did not fully pass"
    ]


def write_csv_outputs(
    out_dir: Path,
    config_results: list[dict[str, object]],
    swap_rows: list[dict[str, object]],
    alt_rows: list[dict[str, object]],
    shape_rows: list[dict[str, object]],
) -> None:
    subset_path = out_dir / "subset_statuses.csv"
    with subset_path.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(
            handle,
            fieldnames=[
                "target_case",
                "config_id",
                "overlap_class",
                "retained_atoms",
                "status",
                "solver_return_code",
            ],
        )
        writer.writeheader()
        for result in config_results:
            for row in result["subset_rows"]:  # type: ignore[index]
                writer.writerow(
                    {
                        "target_case": row["target_case"],
                        "config_id": row["config_id"],
                        "overlap_class": row["overlap_class"],
                        "retained_atoms": "; ".join(row["retained_atoms"]),
                        "status": row["status"],
                        "solver_return_code": row["solver_return_code"],
                    }
                )

    summary_path = out_dir / "configuration_summary.csv"
    with summary_path.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(
            handle,
            fieldnames=[
                "target_case",
                "config_id",
                "overlap_class",
                "full_package_status",
                "subset_count",
                "sat_count",
                "unsat_count",
                "unknown_count",
                "mus_count",
                "mcs_count",
                "duality_passes",
                "rights_free_mus",
                "every_mus_contains_both_rights",
                "singleton_right_mcs_voter0",
                "singleton_right_mcs_voter1",
                "semantic_multiplicity_survives",
            ],
        )
        writer.writeheader()
        for result in config_results:
            counts = result["status_counts"]  # type: ignore[assignment]
            rights = result["rights_analysis"]  # type: ignore[assignment]
            multiplicity = result["mcs_voter_index_multiplicity"]  # type: ignore[assignment]
            by_voter = multiplicity["singleton_right_mcs_by_voter"]
            writer.writerow(
                {
                    "target_case": result["target_case"],
                    "config_id": result["config_id"],
                    "overlap_class": result["overlap_class"],
                    "full_package_status": result["full_package_status"],
                    "subset_count": result["subset_count"],
                    "sat_count": counts["SAT"],
                    "unsat_count": counts["UNSAT"],
                    "unknown_count": counts["UNKNOWN"],
                    "mus_count": result["mus_count"],
                    "mcs_count": result["mcs_count"],
                    "duality_passes": result["duality_passes"],
                    "rights_free_mus": rights["any_mus_contains_neither_right"],
                    "every_mus_contains_both_rights": rights["every_mus_contains_both_rights"],
                    "singleton_right_mcs_voter0": by_voter["voter0"],
                    "singleton_right_mcs_voter1": by_voter["voter1"],
                    "semantic_multiplicity_survives": multiplicity["semantic_voter_indexed_repair_multiplicity_survives"],
                }
            )

    for name, rows in (("voter_swap.csv", swap_rows), ("o2_o3_o4.csv", alt_rows)):
        path = out_dir / name
        with path.open("w", newline="", encoding="utf-8") as handle:
            writer = csv.DictWriter(handle, fieldnames=list(rows[0].keys()))
            writer.writeheader()
            writer.writerows(rows)

    shape_path = out_dir / "shape_signatures.csv"
    with shape_path.open("w", newline="", encoding="utf-8") as handle:
        fieldnames = [
            "target_case",
            "overlap_class",
            "configuration_count",
            "canonical_representative",
            "representative_signature_stable",
            "signature_form_count",
            "structural_signature_form_count",
            "shape_signature_json",
        ]
        writer = csv.DictWriter(handle, fieldnames=fieldnames)
        writer.writeheader()
        for row in shape_rows:
            writer.writerow(
                {
                    "target_case": row["target_case"],
                    "overlap_class": row["overlap_class"],
                    "configuration_count": row["configuration_count"],
                    "canonical_representative": row["canonical_representative"],
                    "representative_signature_stable": row["representative_signature_stable"],
                    "signature_form_count": row["signature_form_count"],
                    "structural_signature_form_count": row["structural_signature_form_count"],
                    "shape_signature_json": json.dumps(row["shape_signature"], sort_keys=True),
                }
            )


def run_precheck(out_dir: Path, solver: str, timeout: float) -> dict[str, object]:
    out_dir.mkdir(parents=True, exist_ok=True)
    config_results = []
    result_by_key: dict[tuple[str, str], dict[str, object]] = {}
    work_dir = out_dir / "work"
    for target in TARGET_RESIDUALS:
        for pair0, pair1 in witness_configs():
            result = run_configuration(
                target=target,
                pair0=pair0,
                pair1=pair1,
                solver=solver,
                timeout=timeout,
                work_dir=work_dir,
            )
            config_results.append(result)
            result_by_key[(target.case_id, result["config_id"])] = result  # type: ignore[index]

    swap_pass, swap_rows = evaluate_voter_swap(result_by_key)
    alt_pass, alt_rows = evaluate_alt_relabeling(result_by_key)
    config_results = attach_shape_signatures(config_results, swap_rows)
    shape_comparison = build_shape_comparison(config_results)
    verdict, reasons = decide_gate(config_results, swap_pass, alt_pass, shape_comparison)
    by_target_class: dict[str, dict[str, int]] = {}
    for result in config_results:
        key = f"{result['target_case']}:{result['overlap_class']}"
        by_target_class.setdefault(key, {"configs": 0, "mus": 0, "mcs": 0})
        by_target_class[key]["configs"] += 1
        by_target_class[key]["mus"] += int(result["mus_count"])
        by_target_class[key]["mcs"] += int(result["mcs_count"])

    payload = {
        "schema_version": 1,
        "out_dir": str(out_dir),
        "solver_metadata": solver_metadata(solver),
        "target_residuals": [
            {
                "case_id": target.case_id,
                "production_levers": list(target.production_levers),
                "base_atoms": list(target.base_atoms),
            }
            for target in TARGET_RESIDUALS
        ],
        "semantic_atom_universe": {
            "base_atoms": list(BASE_ORDER),
            "rights_atom_schema": "right(voter, unordered_alt_pair)",
            "pair_order": [list(pair) for pair in PAIR_ORDER],
            "guard_variables_are_semantic_atoms": False,
        },
        "witness_configuration_count": len(witness_configs()),
        "target_count": len(TARGET_RESIDUALS),
        "configuration_result_count": len(config_results),
        "subset_status_count": sum(int(r["subset_count"]) for r in config_results),
        "configuration_results": [
            {k: v for k, v in result.items() if k != "subset_rows"} for result in config_results
        ],
        "voter_swap": {
            "passes": swap_pass,
            "rows": swap_rows,
        },
        "o2_o3_o4": {
            "alternative_relabeling_passes": alt_pass,
            "rows": alt_rows,
        },
        "shape_comparison": shape_comparison,
        "aggregate_by_target_class": by_target_class,
        "gate_verdict": verdict,
        "gate_reasons": reasons,
        "non_claims": [
            "no M4 theorem implementation",
            "no Lean formalization",
            "no Arrow, Gibbard-Satterthwaite, or general social-choice claim",
            "no production encoding change",
            "no tracked results artifact promotion",
        ],
    }
    (out_dir / "precheck_results.json").write_text(
        json.dumps(payload, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    write_csv_outputs(out_dir, config_results, swap_rows, alt_rows, shape_comparison["rows"])  # type: ignore[index]
    return payload


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--out-dir", type=Path, default=OUT_DEFAULT)
    parser.add_argument("--solver", default="cadical")
    parser.add_argument("--timeout", type=float, default=20.0)
    args = parser.parse_args()
    payload = run_precheck(args.out_dir, args.solver, args.timeout)
    print(json.dumps({
        "out_dir": payload["out_dir"],
        "witness_configuration_count": payload["witness_configuration_count"],
        "configuration_result_count": payload["configuration_result_count"],
        "subset_status_count": payload["subset_status_count"],
        "gate_verdict": payload["gate_verdict"],
        "gate_reasons": payload["gate_reasons"],
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
