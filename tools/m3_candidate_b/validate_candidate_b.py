#!/usr/bin/env python3
"""Fail-closed validator for the frozen Candidate B M3 application package.

The validator treats SAT/UNSAT statuses as artifact-defined Boolean inputs. It
independently recomputes repair minimality, grouping, residual faithfulness,
GroupSoundness, deletion monotonicity, and pointwise grouped correctness. It
does not validate the encoder, solver, semantic meaning of atoms, or Candidate
B in Lean.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import subprocess
import sys
from pathlib import Path
from typing import Any, Dict, FrozenSet, Iterable, List, Mapping, Sequence, Set, Tuple


EVIDENCE_SOURCE_COMMIT = "1c2b9e7b979ba1a4b08c1d69f5400907cf2ca689"
THEOREM_SOURCE_COMMIT = "e33805d0ff0a64f12e450ba7aaa150729901d7d2"
REQUIRED_CLAIM = (
    "Candidate B is an artifact-defined M3-B instantiation under the "
    "declared bundled contract."
)
CONTRACT_ATOMS = ["asymm", "un", "minlib", "no_cycle4"]
IMPLEMENTATION_LEVERS = [
    "asymm",
    "un",
    "decisive_voter0",
    "decisive_voter1",
    "no_cycle4",
]
BUNDLED_BITS = ["asymm", "un", "minlib", "no_cycle3", "no_cycle4"]
SPLIT_BITS = [
    "asymm",
    "un",
    "decisive_voter0",
    "decisive_voter1",
    "no_cycle3",
    "no_cycle4",
]
BLOCK_MAP = {
    "asymm": ["asymm"],
    "un": ["un"],
    "minlib": ["decisive_voter0", "decisive_voter1"],
    "no_cycle4": ["no_cycle4"],
}
FULL_COMPARISON_BLOCK_MAP = dict(BLOCK_MAP, no_cycle3=["no_cycle3"])
THEOREM_FILES = {
    "SocialChoiceAtlas/Reportability/Defs.lean": {
        "git_blob_sha": "03053943a8f2429c79340734a23b0b0609058e9b",
        "content_sha256": "9f776f7da057c1ae8e3f1394119b52ae55902567185823f6fa10ede89fab1e8a",
    },
    "SocialChoiceAtlas/Reportability/GroupSound.lean": {
        "git_blob_sha": "2ef41b003d63088bc762a493c6ed1590d2996293",
        "content_sha256": "fdf0251a3f44e5c1e9cc2b7d4ee580fb500f9370adad29b4f5be07a947f85b5b",
    },
    "SocialChoiceAtlas/Reportability/Monotone.lean": {
        "git_blob_sha": "37958d0c63c835365a8dda94ec615f7e5ff719f4",
        "content_sha256": "4614e5b747d278196d73be882a535c3d53a4e53c2266f12dbdf4fde7ccb89641",
    },
    "SocialChoiceAtlas/Reportability/Examples.lean": {
        "git_blob_sha": "14ce4b823795056f9cb91814acf83fb1b4fedcbe",
        "content_sha256": "27e3decfe1b7100124b4bad8acc4a61128614b86c47e14aa8e513c8d92747fac",
    },
}
THEOREMS = [
    "m3b_grouped_correctness",
    "m3b_two_realization",
    "m3c_converse",
    "groupSoundness_iff",
    "audit_cost_collapse",
]
OUTPUT_NAMES = [
    "residual_faithfulness.json",
    "residual_faithfulness.md",
    "contract_repairs.json",
    "contract_repairs.md",
    "raw_repairs.json",
    "raw_repairs.md",
    "raw_noncanonicity.json",
    "grouped_repairs.json",
    "grouped_repairs.md",
    "group_soundness_full.json",
    "group_soundness_full.md",
    "group_soundness_triangulation.json",
    "psi_deletion_monotonicity.json",
    "psi_deletion_monotonicity.md",
    "grouped_correctness_pointwise.json",
    "grouped_correctness_pointwise.md",
    "audit_result.json",
    "audit_result.md",
]


class AuditFailure(Exception):
    """A mandatory gate failed."""

    def __init__(self, gate: str, message: str):
        super().__init__(message)
        self.gate = gate
        self.message = message


def require(condition: bool, gate: str, message: str) -> None:
    if not condition:
        raise AuditFailure(gate, message)


def exact_keys(obj: Mapping[str, Any], expected: Iterable[str], gate: str, label: str) -> None:
    expected_set = set(expected)
    actual = set(obj)
    require(
        actual == expected_set,
        gate,
        "%s keys differ: missing=%s extra=%s"
        % (label, sorted(expected_set - actual), sorted(actual - expected_set)),
    )


def load_json(path: Path, gate: str, label: str) -> Any:
    try:
        with path.open("r", encoding="utf-8") as handle:
            return json.load(handle)
    except (OSError, json.JSONDecodeError) as exc:
        raise AuditFailure(gate, "%s cannot be read as JSON: %s" % (label, exc.__class__.__name__))


def dump_json(value: Any) -> str:
    return json.dumps(value, ensure_ascii=True, indent=2, sort_keys=True) + "\n"


def write_json(path: Path, value: Any) -> None:
    path.write_text(dump_json(value), encoding="utf-8")


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def git_blob_sha(data: bytes) -> str:
    header = ("blob %d\0" % len(data)).encode("ascii")
    return hashlib.sha1(header + data).hexdigest()


def subsets(universe: Sequence[str]) -> List[FrozenSet[str]]:
    return [
        frozenset(item for index, item in enumerate(universe) if mask & (1 << index))
        for mask in range(1 << len(universe))
    ]


def ordered_items(items: Iterable[str], universe: Sequence[str]) -> List[str]:
    item_set = set(items)
    return [item for item in universe if item in item_set]


def family_json(family: Iterable[FrozenSet[str]], universe: Sequence[str]) -> List[List[str]]:
    rows = [ordered_items(item, universe) for item in family]
    return sorted(rows, key=lambda row: (len(row), [universe.index(item) for item in row]))


def set_label(items: Iterable[str], universe: Sequence[str]) -> str:
    row = ordered_items(items, universe)
    return "{}" if not row else "{" + ", ".join(row) + "}"


def case_bits(retained: FrozenSet[str], bit_order: Sequence[str]) -> str:
    return "".join("1" if item in retained else "0" for item in bit_order)


def case_id(retained: FrozenSet[str], bit_order: Sequence[str]) -> str:
    return "case_" + case_bits(retained, bit_order)


def bit_mask(bits: str) -> int:
    return sum((1 << index) for index, bit in enumerate(bits) if bit == "1")


def beta_set(contract_set: FrozenSet[str]) -> FrozenSet[str]:
    return frozenset(
        lever for atom in contract_set for lever in BLOCK_MAP[atom]
    )


def group_touch_any(raw_deletion: FrozenSet[str]) -> FrozenSet[str]:
    return frozenset(
        atom for atom in CONTRACT_ATOMS if raw_deletion.intersection(BLOCK_MAP[atom])
    )


def minimal_feasible(
    universe: Sequence[str], feasible: Mapping[FrozenSet[str], bool]
) -> Set[FrozenSet[str]]:
    return {
        deletion
        for deletion in subsets(universe)
        if feasible[deletion]
        and not any(
            smaller < deletion and feasible[smaller]
            for smaller in subsets(universe)
        )
    }


def validate_contract(contract: Mapping[str, Any]) -> None:
    gate = "contract_schema"
    exact_keys(
        contract,
        {
            "schema_version",
            "scope",
            "implementation_levers",
            "block_map",
            "grouping",
            "reference_predicate",
            "implementation_predicate",
            "claim",
            "evidence_mode",
            "release_candidate_identity",
        },
        gate,
        "contract",
    )
    require(contract["schema_version"] == "m3-candidate-b-contract-v1", gate, "unexpected schema version")
    exact_keys(contract["scope"], {"n", "m", "active_contract_atoms", "inactive_atoms", "claim_level"}, gate, "contract.scope")
    require(contract["scope"] == {
        "n": 2,
        "m": 4,
        "active_contract_atoms": CONTRACT_ATOMS,
        "inactive_atoms": ["no_cycle3"],
        "claim_level": "artifact-defined",
    }, gate, "declared scope differs from the frozen Candidate B scope")
    require(contract["implementation_levers"] == IMPLEMENTATION_LEVERS, gate, "implementation lever order or membership differs")
    require(contract["block_map"] == BLOCK_MAP, gate, "block map differs from the frozen map")
    require(contract["grouping"] == "touch-any", gate, "grouping must be touch-any")
    require(contract["reference_predicate"] == "bundled-residual-status", gate, "unexpected reference predicate")
    require(contract["implementation_predicate"] == "split-residual-status", gate, "unexpected implementation predicate")
    require(contract["claim"] == REQUIRED_CLAIM, gate, "required claim wording changed")
    require(contract["evidence_mode"] == "artifact-recomputed", gate, "freeze requires artifact-recomputed mode")
    require(contract["release_candidate_identity"] == "m3-candidate-b-evidence-v1-rc1", gate, "release candidate identity changed")
    seen: Set[str] = set()
    for atom in CONTRACT_ATOMS:
        block = contract["block_map"][atom]
        require(bool(block), gate, "block for %s is empty" % atom)
        require(not seen.intersection(block), gate, "implementation blocks overlap")
        seen.update(block)
    require(seen == set(IMPLEMENTATION_LEVERS), gate, "block map does not cover the implementation interface exactly")


def validate_case_schema(schema: Mapping[str, Any]) -> None:
    gate = "case_schema"
    exact_keys(schema, {"schema_version", "bit_value_semantics", "application_filter", "bundled", "split"}, gate, "case schema")
    require(schema["schema_version"] == "m3-candidate-b-case-schema-v1", gate, "unexpected case schema version")
    require(schema["bit_value_semantics"] == "one-means-retained-active", gate, "bit semantics changed")
    require(schema["application_filter"] == {"no_cycle3": 0}, gate, "no_cycle3 must be fixed inactive")
    expected = {
        "bundled": {
            "representation": "bundled",
            "bit_order": BUNDLED_BITS,
            "case_prefix": "case_",
            "expected_atlas_rows": 32,
            "application_rows": 16,
            "mask_integer_encoding": "little-endian-bit-index-sum",
        },
        "split": {
            "representation": "split",
            "bit_order": SPLIT_BITS,
            "case_prefix": "case_",
            "expected_atlas_rows": 64,
            "application_rows": 32,
            "mask_integer_encoding": "little-endian-bit-index-sum",
        },
    }
    for label in ("bundled", "split"):
        exact_keys(schema[label], expected[label], gate, "case schema.%s" % label)
        require(schema[label] == expected[label], gate, "%s case schema changed" % label)


def git_tree(repo_root: Path, commit: str, gate: str) -> Dict[str, str]:
    try:
        output = subprocess.check_output(
            ["git", "ls-tree", "-r", commit], cwd=str(repo_root), stderr=subprocess.DEVNULL
        ).decode("utf-8")
    except (OSError, subprocess.CalledProcessError, UnicodeDecodeError):
        raise AuditFailure(gate, "recorded source commit is not available in this checkout")
    result: Dict[str, str] = {}
    for line in output.splitlines():
        metadata, path = line.split("\t", 1)
        _mode, kind, blob = metadata.split()
        if kind == "blob":
            result[path] = blob
    return result


def validate_source_artifacts(
    source: Mapping[str, Any], package_root: Path, evidence_root: Path,
    repo_root: Path, verify_git_source: bool,
) -> None:
    gate = "source_artifact_binding"
    exact_keys(source, {"schema_version", "source_commit", "evidence_root", "whitelist_policy", "entries"}, gate, "source artifacts")
    require(source["schema_version"] == "m3-candidate-b-source-artifacts-v1", gate, "unexpected source-artifact schema")
    require(source["source_commit"] == EVIDENCE_SOURCE_COMMIT, gate, "Candidate B evidence source commit changed")
    require(source["evidence_root"] == "m3/candidate_b/evidence", gate, "evidence root changed")
    require(source["whitelist_policy"] == "exact-paths-only", gate, "whitelist policy changed")
    require(isinstance(source["entries"], list) and source["entries"], gate, "source entry list is empty")
    tree = git_tree(repo_root, source["source_commit"], gate) if verify_git_source else {}
    listed: Set[str] = set()
    source_paths: Set[str] = set()
    for index, entry in enumerate(source["entries"]):
        exact_keys(entry, {"source_path", "source_blob_sha", "content_sha256", "package_path"}, gate, "source entry %d" % index)
        package_path = entry["package_path"]
        source_path = entry["source_path"]
        require(isinstance(package_path, str) and package_path.startswith("evidence/"), gate, "package path must stay under evidence/")
        require(".." not in Path(package_path).parts and not Path(package_path).is_absolute(), gate, "unsafe package path")
        require(package_path not in listed, gate, "duplicate package path")
        require(source_path not in source_paths, gate, "duplicate source path")
        listed.add(package_path)
        source_paths.add(source_path)
        path = package_root / package_path
        require(path.is_file(), gate, "whitelisted evidence file is missing: %s" % package_path)
        data = path.read_bytes()
        require(sha256_bytes(data) == entry["content_sha256"], gate, "content hash mismatch: %s" % package_path)
        require(git_blob_sha(data) == entry["source_blob_sha"], gate, "Git blob hash mismatch: %s" % package_path)
        if verify_git_source:
            require(tree.get(source_path) == entry["source_blob_sha"], gate, "source commit/path binding mismatch: %s" % source_path)
    actual = {
        "evidence/" + path.relative_to(evidence_root).as_posix()
        for path in evidence_root.rglob("*") if path.is_file()
    }
    require(actual == listed, gate, "evidence whitelist closure failed: missing=%s extra=%s" % (sorted(listed - actual), sorted(actual - listed)))


ATLAS_KEYS = {
    "axiom_universe", "cases", "cases_total", "experiment", "generated_at_utc",
    "n_alternatives", "n_voters", "representation", "scope_note", "status_counts",
}
CASE_KEYS = {
    "axioms_off", "axioms_on", "case_id", "duration_sec", "files", "manifest",
    "mask_bits", "mask_int", "representation", "solved", "solver", "status",
}
EMBEDDED_MANIFEST_KEYS = {
    "category_counts", "cnf_sha256", "encoding", "minlib", "nclauses", "nvars",
}


def validate_atlas(
    atlas: Mapping[str, Any], spec: Mapping[str, Any], label: str
) -> Dict[str, Mapping[str, Any]]:
    gate = "evidence_schema"
    exact_keys(atlas, ATLAS_KEYS, gate, "%s atlas" % label)
    universe = spec["bit_order"]
    require(atlas["axiom_universe"] == universe, gate, "%s atlas bit order differs" % label)
    require(atlas["representation"] == label, gate, "%s representation field differs" % label)
    require(atlas["experiment"] == "candidate_b_minlib_granularity", gate, "%s experiment differs" % label)
    require(atlas["n_voters"] == 2 and atlas["n_alternatives"] == 4, gate, "%s scope differs" % label)
    require(atlas["cases_total"] == spec["expected_atlas_rows"], gate, "%s case total differs" % label)
    require(isinstance(atlas["cases"], list) and len(atlas["cases"]) == spec["expected_atlas_rows"], gate, "%s case list is incomplete" % label)
    result: Dict[str, Mapping[str, Any]] = {}
    status_counts = {"SAT": 0, "UNSAT": 0}
    for mask, row in enumerate(atlas["cases"]):
        exact_keys(row, CASE_KEYS, gate, "%s case row" % label)
        bits = "".join("1" if mask & (1 << index) else "0" for index in range(len(universe)))
        expected_id = "case_" + bits
        on = [item for index, item in enumerate(universe) if mask & (1 << index)]
        off = [item for item in universe if item not in on]
        require(row["case_id"] == expected_id, "case_schema", "%s case ID does not follow bit order" % label)
        require(row["mask_bits"] == bits and row["mask_int"] == mask, "case_schema", "%s mask encoding differs" % label)
        require(row["axioms_on"] == on and row["axioms_off"] == off, "case_schema", "%s retained set and case ID disagree" % label)
        require(row["representation"] == label, gate, "%s case representation differs" % label)
        require(row["solved"] is True and row["status"] in ("SAT", "UNSAT"), gate, "%s case is not solved SAT/UNSAT" % label)
        exact_keys(row["files"], {"cnf", "manifest", "solver_log", "summary"}, gate, "%s case files" % label)
        exact_keys(row["manifest"], EMBEDDED_MANIFEST_KEYS, gate, "%s embedded manifest" % label)
        require(re.fullmatch(r"[0-9a-f]{64}", row["manifest"]["cnf_sha256"]) is not None, gate, "%s CNF hash is malformed" % label)
        require(expected_id not in result, gate, "%s duplicate case ID" % label)
        result[expected_id] = row
        status_counts[row["status"]] += 1
    require(atlas["status_counts"] == status_counts, gate, "%s status counts disagree with rows" % label)
    return result


def validate_case_files(
    evidence_root: Path, label: str, rows: Mapping[str, Mapping[str, Any]],
    application_universe: Sequence[str], bit_order: Sequence[str],
) -> None:
    gate = "evidence_schema"
    for retained in subsets(application_universe):
        full_retained = frozenset(retained)
        cid = case_id(full_retained, bit_order)
        require(cid in rows, gate, "%s application row missing: %s" % (label, cid))
        row = rows[cid]
        require("no_cycle3" in row["axioms_off"], "case_schema", "%s application row activates no_cycle3" % label)
        summary_path = evidence_root / label / cid / "summary.json"
        manifest_path = evidence_root / label / cid / "sen24.manifest.json"
        summary = load_json(summary_path, gate, "%s summary %s" % (label, cid))
        manifest = load_json(manifest_path, gate, "%s manifest %s" % (label, cid))
        require(summary == row, gate, "%s summary differs from atlas row: %s" % (label, cid))
        for key in EMBEDDED_MANIFEST_KEYS:
            require(key in manifest, gate, "%s source manifest lacks %s" % (label, key))
            require(manifest[key] == row["manifest"][key], gate, "%s source manifest differs at %s: %s" % (label, key, cid))


COMPARISON_KEYS = {
    "bundled_universe", "candidate_b_assessment", "date", "experiment",
    "generated_at_utc", "logical_relation", "mapped_cases", "n_alternatives",
    "n_voters", "one_sided_split_cases", "repair_comparison", "scope_note",
    "split_universe",
}
MAPPED_CASE_KEYS = {
    "bundled_case_id", "bundled_package", "bundled_package_key", "bundled_status",
    "clause_multiset_equal", "split_case_id", "split_package", "split_package_key",
    "split_status", "status_equal",
}


def validate_comparison(
    comparison: Mapping[str, Any], bundled_rows: Mapping[str, Mapping[str, Any]],
    split_rows: Mapping[str, Mapping[str, Any]],
) -> List[Mapping[str, Any]]:
    gate = "residual_faithfulness"
    exact_keys(comparison, COMPARISON_KEYS, "evidence_schema", "comparison")
    require(comparison["bundled_universe"] == BUNDLED_BITS, "case_schema", "comparison bundled bit order differs")
    require(comparison["split_universe"] == SPLIT_BITS, "case_schema", "comparison split bit order differs")
    require(isinstance(comparison["mapped_cases"], list) and len(comparison["mapped_cases"]) == 32, gate, "comparison must contain exactly 32 mapped rows")
    seen_bundled: Set[str] = set()
    application_rows: List[Mapping[str, Any]] = []
    for row in comparison["mapped_cases"]:
        exact_keys(row, MAPPED_CASE_KEYS, "evidence_schema", "comparison mapped row")
        bcid = row["bundled_case_id"]
        scid = row["split_case_id"]
        require(bcid not in seen_bundled, gate, "duplicate mapped bundled row: %s" % bcid)
        seen_bundled.add(bcid)
        require(bcid in bundled_rows and scid in split_rows, gate, "mapped case ID is absent from an atlas")
        bundled_retained = frozenset(bundled_rows[bcid]["axioms_on"])
        split_retained = frozenset(
            lever for atom in bundled_retained for lever in FULL_COMPARISON_BLOCK_MAP[atom]
        )
        require(scid == case_id(split_retained, SPLIT_BITS), gate, "mapped split case ID disagrees with block map")
        require(row["bundled_package"] == ordered_items(bundled_retained, BUNDLED_BITS), gate, "mapped bundled package disagrees")
        require(row["split_package"] == ordered_items(split_retained, SPLIT_BITS), gate, "mapped split package disagrees")
        require(row["bundled_status"] == bundled_rows[bcid]["status"], gate, "mapped bundled status disagrees with atlas")
        require(row["split_status"] == split_rows[scid]["status"], gate, "mapped split status disagrees with atlas")
        require(row["status_equal"] == (row["bundled_status"] == row["split_status"]), gate, "status_equal field disagrees")
        require(row["clause_multiset_equal"] is True, "precomputed_claim_crosscheck", "recorded clause-multiset cross-check is not true")
        if "no_cycle3" not in bundled_retained:
            application_rows.append(row)
    require(len(seen_bundled) == 32, gate, "mapped comparison is not closed over bundled cases")
    require(len(application_rows) == 16, gate, "application mapping must contain exactly 16 no_cycle3-off rows")
    return application_rows


def validate_theorem_binding(binding: Mapping[str, Any], repo_root: Path, verify_git_source: bool) -> None:
    gate = "theorem_binding"
    keys = {
        "schema_version", "claim", "source_commit", "lean_toolchain", "lean_files",
        "theorems", "focused_smoke_gate", "focused_smoke_sha256", "expected_axioms",
        "theorem_core_smoke", "axiom_audit_result", "candidate_b_formalized_in_lean",
        "not_claimed",
    }
    exact_keys(binding, keys, gate, "theorem binding")
    require(binding["schema_version"] == "m3-candidate-b-theorem-binding-v1", gate, "unexpected theorem-binding schema")
    require(binding["claim"] == REQUIRED_CLAIM, gate, "theorem-binding claim wording changed")
    require(binding["source_commit"] == THEOREM_SOURCE_COMMIT, gate, "theorem-core source commit changed")
    require(binding["lean_toolchain"] == "leanprover/lean4:v4.15.0", gate, "Lean toolchain binding changed")
    require(binding["lean_files"] == THEOREM_FILES, gate, "Lean file binding differs")
    require(binding["theorems"] == THEOREMS, gate, "bound theorem list differs")
    require(binding["focused_smoke_gate"] == "scripts/ci_m3_smoke.sh", gate, "focused smoke path changed")
    require(binding["focused_smoke_sha256"] == "31efce4413f5a7803a5dd803a7cb07fe1aae078fc06a923f1a87fc5bcebb030b", gate, "focused smoke hash changed")
    require(binding["expected_axioms"] == ["Classical.choice", "Quot.sound", "propext"], gate, "expected axiom set changed")
    require(binding["theorem_core_smoke"] == "PASS" and binding["axiom_audit_result"] == "PASS", gate, "Lean smoke or axiom audit is not recorded PASS")
    require(binding["candidate_b_formalized_in_lean"] is False, gate, "Candidate B must not be marked Lean-formalized")
    required_nonclaims = {
        "Candidate B is formalized in Lean",
        "artifact semantics are proved in Lean",
        "CNF generation is proved correct",
    }
    require(required_nonclaims.issubset(set(binding["not_claimed"])), gate, "mandatory Lean non-claims are missing")
    tree = git_tree(repo_root, binding["source_commit"], gate) if verify_git_source else {}
    combined_text = ""
    for path_text, hashes in THEOREM_FILES.items():
        path = repo_root / path_text
        require(path.is_file(), gate, "bound Lean file is absent: %s" % path_text)
        data = path.read_bytes()
        require(sha256_bytes(data) == hashes["content_sha256"], gate, "Lean content hash mismatch: %s" % path_text)
        require(git_blob_sha(data) == hashes["git_blob_sha"], gate, "Lean blob hash mismatch: %s" % path_text)
        if verify_git_source:
            require(tree.get(path_text) == hashes["git_blob_sha"], gate, "Lean source-commit binding mismatch: %s" % path_text)
        combined_text += data.decode("utf-8")
    for theorem in THEOREMS:
        require(re.search(r"\btheorem\s+" + re.escape(theorem) + r"\b", combined_text) is not None, gate, "bound theorem declaration not found: %s" % theorem)
    smoke = repo_root / binding["focused_smoke_gate"]
    require(smoke.is_file() and sha256_bytes(smoke.read_bytes()) == binding["focused_smoke_sha256"], gate, "focused smoke gate hash mismatch")


def crosscheck_precomputed_repairs(
    comparison: Mapping[str, Any], contract_repairs: Set[FrozenSet[str]],
    raw_repairs: Set[FrozenSet[str]],
) -> None:
    gate = "precomputed_claim_crosscheck"
    require(isinstance(comparison["repair_comparison"], list), gate, "repair comparison must be a list")
    matches = [row for row in comparison["repair_comparison"] if row.get("bundled_case_id") == "case_11101"]
    require(len(matches) == 1, gate, "exactly one no_cycle3-off repair comparison is required")
    row = matches[0]
    require(isinstance(row.get("bundled_min_repairs"), list), gate, "bundled repair cross-check is malformed")
    require(isinstance(row.get("split_min_repairs"), list), gate, "split repair cross-check is malformed")
    for name in row["bundled_min_repairs"]:
        require(name in CONTRACT_ATOMS, gate, "unknown or non-singleton bundled repair cross-check")
    for name in row["split_min_repairs"]:
        require(name in IMPLEMENTATION_LEVERS, gate, "unknown or non-singleton split repair cross-check")
    recorded_contract = {frozenset([name]) for name in row["bundled_min_repairs"]}
    recorded_raw = {frozenset([name]) for name in row["split_min_repairs"]}
    require(recorded_contract == contract_repairs, gate, "recorded bundled repair family differs from independent recomputation")
    require(recorded_raw == raw_repairs, gate, "recorded split repair family differs from independent recomputation")


def table_markdown(title: str, headers: Sequence[str], rows: Sequence[Sequence[Any]], summary: Sequence[str]) -> str:
    lines = ["# " + title, "", "| " + " | ".join(headers) + " |", "|" + "|".join(["---"] * len(headers)) + "|"]
    for row in rows:
        lines.append("| " + " | ".join(str(item) for item in row) + " |")
    lines.extend([""] + list(summary) + [""])
    return "\n".join(lines)


def clear_outputs(out_dir: Path) -> None:
    out_dir.mkdir(parents=True, exist_ok=True)
    for name in OUTPUT_NAMES:
        path = out_dir / name
        if path.exists():
            path.unlink()


def validate_package(
    contract_path: Path,
    case_schema_path: Path,
    source_artifacts_path: Path,
    evidence_root: Path,
    theorem_binding_path: Path,
    out_dir: Path,
    repo_root: Path,
    verify_git_source: bool = True,
) -> Dict[str, Any]:
    clear_outputs(out_dir)
    contract = load_json(contract_path, "contract_schema", "contract")
    case_schema = load_json(case_schema_path, "case_schema", "case schema")
    source = load_json(source_artifacts_path, "source_artifact_binding", "source artifacts")
    binding = load_json(theorem_binding_path, "theorem_binding", "theorem binding")
    validate_contract(contract)
    validate_case_schema(case_schema)
    package_root = contract_path.parent
    validate_source_artifacts(source, package_root, evidence_root, repo_root, verify_git_source)
    validate_theorem_binding(binding, repo_root, verify_git_source)

    comparison = load_json(evidence_root / "comparison.json", "evidence_schema", "comparison")
    bundled_atlas = load_json(evidence_root / "bundled" / "atlas.json", "evidence_schema", "bundled atlas")
    split_atlas = load_json(evidence_root / "split" / "atlas.json", "evidence_schema", "split atlas")
    bundled_rows = validate_atlas(bundled_atlas, case_schema["bundled"], "bundled")
    split_rows = validate_atlas(split_atlas, case_schema["split"], "split")
    validate_case_files(evidence_root, "bundled", bundled_rows, CONTRACT_ATOMS, BUNDLED_BITS)
    validate_case_files(evidence_root, "split", split_rows, IMPLEMENTATION_LEVERS, SPLIT_BITS)
    mapped_application_rows = validate_comparison(comparison, bundled_rows, split_rows)

    residual_rows: List[Dict[str, Any]] = []
    residual_mismatches = 0
    for retained in subsets(CONTRACT_ATOMS):
        bcid = case_id(retained, BUNDLED_BITS)
        split_retained = beta_set(retained)
        scid = case_id(split_retained, SPLIT_BITS)
        bstatus = bundled_rows[bcid]["status"]
        sstatus = split_rows[scid]["status"]
        match = bstatus == sstatus
        residual_mismatches += 0 if match else 1
        residual_rows.append({
            "retained_contract_atoms": ordered_items(retained, CONTRACT_ATOMS),
            "bundled_case_id": bcid,
            "bundled_status": bstatus,
            "split_case_id": scid,
            "split_status": sstatus,
            "match": match,
        })
    full_bundled = bundled_rows[case_id(frozenset(CONTRACT_ATOMS), BUNDLED_BITS)]["status"]
    full_split = split_rows[case_id(frozenset(IMPLEMENTATION_LEVERS), SPLIT_BITS)]["status"]
    require(full_bundled == "UNSAT", "fully_active_bundled", "fully active bundled row is not UNSAT")
    require(full_split == "UNSAT", "fully_active_split", "fully active split row is not UNSAT")
    require(len(mapped_application_rows) == 16, "residual_faithfulness", "comparison application row count changed")
    require(residual_mismatches == 0, "residual_faithfulness", "bundled/split status mismatch")
    require(all(row["bundled_status"] == "SAT" and row["split_status"] == "SAT" for row in residual_rows if len(row["retained_contract_atoms"]) < 4), "residual_faithfulness", "a proper block-aligned residual is not SAT/SAT")

    contract_feasible: Dict[FrozenSet[str], bool] = {}
    for deletion in subsets(CONTRACT_ATOMS):
        retained = frozenset(set(CONTRACT_ATOMS) - set(deletion))
        contract_feasible[deletion] = bundled_rows[case_id(retained, BUNDLED_BITS)]["status"] == "SAT"
    contract_repairs = minimal_feasible(CONTRACT_ATOMS, contract_feasible)

    raw_feasible: Dict[FrozenSet[str], bool] = {}
    for deletion in subsets(IMPLEMENTATION_LEVERS):
        retained = frozenset(set(IMPLEMENTATION_LEVERS) - set(deletion))
        raw_feasible[deletion] = split_rows[case_id(retained, SPLIT_BITS)]["status"] == "SAT"
    raw_repairs = minimal_feasible(IMPLEMENTATION_LEVERS, raw_feasible)
    require(frozenset() not in raw_repairs, "raw_repairs", "zero deletion cannot be a repair")
    require(len(raw_feasible) == 32, "raw_repairs", "split application lattice is not closed")
    crosscheck_precomputed_repairs(comparison, contract_repairs, raw_repairs)

    transported_contract = {beta_set(repair) for repair in contract_repairs}
    raw_noncanonical = transported_contract != raw_repairs
    minlib_pair = frozenset(["decisive_voter0", "decisive_voter1"])
    require(raw_noncanonical and minlib_pair in transported_contract and minlib_pair not in raw_repairs, "raw_noncanonicity", "raw non-canonicity witness was not reproduced")
    require(frozenset(["decisive_voter0"]) in raw_repairs and frozenset(["decisive_voter1"]) in raw_repairs, "raw_noncanonicity", "person-specific singleton repairs are missing")

    raw_group_rows = [
        {"raw_repair": ordered_items(repair, IMPLEMENTATION_LEVERS), "grouped_report": ordered_items(group_touch_any(repair), CONTRACT_ATOMS)}
        for repair in sorted(raw_repairs, key=lambda item: ordered_items(item, IMPLEMENTATION_LEVERS))
    ]
    grouped_image = {group_touch_any(repair) for repair in raw_repairs}
    grouped_repairs = {
        group for group in grouped_image
        if not any(smaller < group for smaller in grouped_image)
    }

    group_sound_rows: List[Dict[str, Any]] = []
    group_sound_violations = 0
    for deletion in subsets(IMPLEMENTATION_LEVERS):
        retained_impl = frozenset(set(IMPLEMENTATION_LEVERS) - set(deletion))
        split_cid = case_id(retained_impl, SPLIT_BITS)
        split_status = split_rows[split_cid]["status"]
        grouped = group_touch_any(deletion)
        retained_contract = frozenset(set(CONTRACT_ATOMS) - set(grouped))
        bundled_cid = case_id(retained_contract, BUNDLED_BITS)
        bundled_status = bundled_rows[bundled_cid]["status"]
        implication = split_status != "SAT" or bundled_status == "SAT"
        group_sound_violations += 0 if implication else 1
        group_sound_rows.append({
            "implementation_deletion": ordered_items(deletion, IMPLEMENTATION_LEVERS),
            "retained_implementation": ordered_items(retained_impl, IMPLEMENTATION_LEVERS),
            "split_case_id": split_cid,
            "split_status": split_status,
            "grouped_contract_deletion": ordered_items(grouped, CONTRACT_ATOMS),
            "retained_contract": ordered_items(retained_contract, CONTRACT_ATOMS),
            "bundled_case_id": bundled_cid,
            "bundled_status": bundled_status,
            "implication_result": "PASS" if implication else "FAIL",
        })
    require(len(group_sound_rows) == 32 and group_sound_violations == 0, "group_soundness", "direct exhaustive GroupSoundness failed")

    collapsed_rows: List[Dict[str, Any]] = []
    collapsed_violations = 0
    for repair in raw_repairs:
        grouped = group_touch_any(repair)
        retained = frozenset(set(CONTRACT_ATOMS) - set(grouped))
        cid = case_id(retained, BUNDLED_BITS)
        status = bundled_rows[cid]["status"]
        ok = status == "SAT"
        collapsed_violations += 0 if ok else 1
        collapsed_rows.append({
            "raw_repair": ordered_items(repair, IMPLEMENTATION_LEVERS),
            "grouped_contract_deletion": ordered_items(grouped, CONTRACT_ATOMS),
            "bundled_case_id": cid,
            "bundled_status": status,
            "result": "PASS" if ok else "FAIL",
        })

    monotonicity_rows: List[Dict[str, Any]] = []
    premises_true = 0
    monotonicity_violations = 0
    for retained_large in subsets(CONTRACT_ATOMS):
        large_status = bundled_rows[case_id(retained_large, BUNDLED_BITS)]["status"]
        for retained_small in subsets(CONTRACT_ATOMS):
            if retained_small.issubset(retained_large):
                small_status = bundled_rows[case_id(retained_small, BUNDLED_BITS)]["status"]
                premise = large_status == "SAT"
                premises_true += 1 if premise else 0
                ok = not premise or small_status == "SAT"
                monotonicity_violations += 0 if ok else 1
                monotonicity_rows.append({
                    "retained_subset": ordered_items(retained_small, CONTRACT_ATOMS),
                    "retained_superset": ordered_items(retained_large, CONTRACT_ATOMS),
                    "superset_status": large_status,
                    "subset_status": small_status,
                    "implication_result": "PASS" if ok else "FAIL",
                })
    require(len(monotonicity_rows) == 81 and monotonicity_violations == 0, "psi_deletion_monotonicity", "bundled deletion monotonicity failed")
    require(collapsed_violations == 0, "group_soundness_triangulation", "raw-minimal collapsed GroupSoundness audit failed")

    pointwise_rows: List[Dict[str, Any]] = []
    pointwise_mismatches = 0
    for deletion in subsets(CONTRACT_ATOMS):
        grouped_value = deletion in grouped_repairs
        contract_value = deletion in contract_repairs
        match = grouped_value == contract_value
        pointwise_mismatches += 0 if match else 1
        pointwise_rows.append({
            "contract_deletion": ordered_items(deletion, CONTRACT_ATOMS),
            "grouped_repair": grouped_value,
            "contract_repair": contract_value,
            "match": match,
        })
    require(len(pointwise_rows) == 16 and pointwise_mismatches == 0, "pointwise_grouped_correctness", "GroupedRepair and ContractRepair differ pointwise")

    residual_output = {
        "schema_version": "m3-candidate-b-residual-faithfulness-v1",
        "rows_expected": 16,
        "rows_observed": len(residual_rows),
        "mismatches": residual_mismatches,
        "fully_active": {"bundled": full_bundled, "split": full_split},
        "proper_residuals": "SAT / SAT",
        "rows": residual_rows,
        "result": "PASS",
    }
    contract_output = {
        "schema_version": "m3-candidate-b-contract-repairs-v1",
        "deletions_checked": 16,
        "repairs": family_json(contract_repairs, CONTRACT_ATOMS),
        "result": "PASS",
    }
    raw_output = {
        "schema_version": "m3-candidate-b-raw-repairs-v1",
        "deletions_checked": 32,
        "repairs": family_json(raw_repairs, IMPLEMENTATION_LEVERS),
        "non_singleton_minimal_repairs": [row for row in family_json(raw_repairs, IMPLEMENTATION_LEVERS) if len(row) > 1],
        "result": "PASS",
    }
    raw_noncanonicity_output = {
        "schema_version": "m3-candidate-b-raw-noncanonicity-v1",
        "transported_bundled_family": family_json(transported_contract, IMPLEMENTATION_LEVERS),
        "split_raw_family": family_json(raw_repairs, IMPLEMENTATION_LEVERS),
        "families_equal": False,
        "raw_repair_canonicity": "FAIL",
        "result": "PASS",
    }
    grouped_output = {
        "schema_version": "m3-candidate-b-grouped-repairs-v1",
        "raw_to_grouped": raw_group_rows,
        "grouped_image": family_json(grouped_image, CONTRACT_ATOMS),
        "grouped_repairs": family_json(grouped_repairs, CONTRACT_ATOMS),
        "result": "PASS",
    }
    group_sound_output = {
        "schema_version": "m3-candidate-b-group-soundness-full-v1",
        "implementation_deletions_checked": 32,
        "feasible_split_residuals": sum(1 for row in group_sound_rows if row["split_status"] == "SAT"),
        "violations": group_sound_violations,
        "rows": group_sound_rows,
        "result": "PASS",
    }
    triangulation_output = {
        "schema_version": "m3-candidate-b-group-soundness-triangulation-v1",
        "direct_exhaustive": {"deletions_checked": 32, "violations": 0, "result": "PASS"},
        "raw_minimal_only": {"repairs_checked": len(collapsed_rows), "violations": collapsed_violations, "rows": sorted(collapsed_rows, key=lambda row: row["raw_repair"]), "result": "PASS"},
        "psi_deletion_monotonicity": "PASS",
        "verdicts_agree": True,
        "result": "PASS",
    }
    monotonicity_output = {
        "schema_version": "m3-candidate-b-psi-deletion-monotonicity-v1",
        "comparable_pairs_checked": len(monotonicity_rows),
        "premises_true": premises_true,
        "violations": monotonicity_violations,
        "counterexample_rows": [],
        "rows": monotonicity_rows,
        "result": "PASS",
    }
    pointwise_output = {
        "schema_version": "m3-candidate-b-grouped-correctness-pointwise-v1",
        "points_checked": len(pointwise_rows),
        "mismatches": pointwise_mismatches,
        "true_points": family_json(contract_repairs, CONTRACT_ATOMS),
        "rows": pointwise_rows,
        "raw_repair_canonicity": "FAIL",
        "artifact_defined_grouped_correctness": "PASS",
        "result": "PASS",
    }
    audit_result = {
        "schema_version": "m3-candidate-b-audit-v1",
        "overall": "PASS",
        "scope": "artifact-defined",
        "claim": REQUIRED_CLAIM,
        "evidence_mode": "artifact-recomputed",
        "fully_active_bundled_unsat": True,
        "fully_active_split_unsat": True,
        "residual_faithfulness": {"rows_expected": 16, "rows_observed": 16, "mismatches": 0, "result": "PASS"},
        "raw_noncanonicity": {"result": "PASS"},
        "raw_repairs": family_json(raw_repairs, IMPLEMENTATION_LEVERS),
        "grouped_repairs": family_json(grouped_repairs, CONTRACT_ATOMS),
        "contract_repairs": family_json(contract_repairs, CONTRACT_ATOMS),
        "group_soundness": {"implementation_deletions_checked": 32, "violations": 0, "result": "PASS"},
        "psi_deletion_monotonicity": {"comparable_pairs_checked": 81, "violations": 0, "result": "PASS"},
        "pointwise_grouped_correctness": {"points_checked": 16, "mismatches": 0, "result": "PASS"},
        "lean_binding": {"candidate_b_formalized_in_lean": False, "theorem_core_smoke": "PASS", "axiom_audit": "PASS"},
        "solver_replay": "NOT RUN",
        "proof_replay": "NOT AVAILABLE IN CURATED PACKAGE",
        "guarantee_ceiling": [
            "artifact-defined contract only",
            "no semantic contract validity claim",
            "no encoder correctness claim",
            "no solver correctness claim",
            "no family-scale claim",
        ],
    }

    outputs = {
        "residual_faithfulness.json": residual_output,
        "contract_repairs.json": contract_output,
        "raw_repairs.json": raw_output,
        "raw_noncanonicity.json": raw_noncanonicity_output,
        "grouped_repairs.json": grouped_output,
        "group_soundness_full.json": group_sound_output,
        "group_soundness_triangulation.json": triangulation_output,
        "psi_deletion_monotonicity.json": monotonicity_output,
        "grouped_correctness_pointwise.json": pointwise_output,
        "audit_result.json": audit_result,
    }
    for name, value in outputs.items():
        write_json(out_dir / name, value)

    (out_dir / "residual_faithfulness.md").write_text(table_markdown(
        "Residual Faithfulness", ["Retained T", "Bundled", "Status", "Split", "Status", "Match"],
        [[set_label(row["retained_contract_atoms"], CONTRACT_ATOMS), "`%s`" % row["bundled_case_id"], row["bundled_status"], "`%s`" % row["split_case_id"], row["split_status"], "PASS" if row["match"] else "FAIL"] for row in residual_rows],
        ["Rows: 16/16. Mismatches: 0. Result: **PASS**."],
    ), encoding="utf-8")
    (out_dir / "contract_repairs.md").write_text(table_markdown(
        "Contract Repairs", ["Repair"], [[set_label(row, CONTRACT_ATOMS)] for row in family_json(contract_repairs, CONTRACT_ATOMS)],
        ["All 16 contract deletions were evaluated. Result: **PASS**."],
    ), encoding="utf-8")
    (out_dir / "raw_repairs.md").write_text(table_markdown(
        "Raw Repairs", ["Repair"], [[set_label(row, IMPLEMENTATION_LEVERS)] for row in family_json(raw_repairs, IMPLEMENTATION_LEVERS)],
        ["All 32 implementation deletions were evaluated. Non-singleton minimal repairs: 0. Result: **PASS**."],
    ), encoding="utf-8")
    (out_dir / "grouped_repairs.md").write_text(table_markdown(
        "Grouped Repairs", ["Raw repair", "Touch-any report"],
        [[set_label(row["raw_repair"], IMPLEMENTATION_LEVERS), set_label(row["grouped_report"], CONTRACT_ATOMS)] for row in raw_group_rows],
        ["GroupedRepair equals ContractRepair over the declared finite contract. Result: **PASS**."],
    ), encoding="utf-8")
    (out_dir / "group_soundness_full.md").write_text(table_markdown(
        "Direct Exhaustive GroupSoundness", ["Deletion R", "Split", "Group", "Bundled", "Result"],
        [[set_label(row["implementation_deletion"], IMPLEMENTATION_LEVERS), "%s %s" % (row["split_case_id"], row["split_status"]), set_label(row["grouped_contract_deletion"], CONTRACT_ATOMS), "%s %s" % (row["bundled_case_id"], row["bundled_status"]), row["implication_result"]] for row in group_sound_rows],
        ["Implementation deletions: 32/32. Violations: 0. Result: **PASS**."],
    ), encoding="utf-8")
    (out_dir / "psi_deletion_monotonicity.md").write_text(table_markdown(
        "Psi Deletion Monotonicity", ["Comparable pairs", "True premises", "Violations", "Result"],
        [[81, premises_true, 0, "PASS"]], ["All ordered subset pairs were evaluated directly."],
    ), encoding="utf-8")
    (out_dir / "grouped_correctness_pointwise.md").write_text(table_markdown(
        "Pointwise Grouped Correctness", ["Deletion G", "GroupedRepair", "ContractRepair", "Match"],
        [[set_label(row["contract_deletion"], CONTRACT_ATOMS), row["grouped_repair"], row["contract_repair"], "PASS" if row["match"] else "FAIL"] for row in pointwise_rows],
        ["Points: 16/16. Mismatches: 0.", "", "Raw repair canonicity: **FAIL**", "", "Artifact-defined grouped correctness: **PASS**"],
    ), encoding="utf-8")
    (out_dir / "audit_result.md").write_text(
        "# Candidate B M3 Application Audit\n\n"
        "Overall: **PASS**\n\n"
        "Evidence mode: `artifact-recomputed`\n\n"
        "> %s\n\n" % REQUIRED_CLAIM
        + "- ResidualFaithfulness: PASS (16/16, 0 mismatches)\n"
        + "- ContractRepair: PASS (16 deletions recomputed)\n"
        + "- RawRepair: PASS (32 deletions recomputed)\n"
        + "- Direct GroupSoundness: PASS (32 implications, 0 violations)\n"
        + "- PsiDeletionMonotonicity: PASS (81 comparable pairs)\n"
        + "- Pointwise grouped correctness: PASS (16 points, 0 mismatches)\n"
        + "- Raw repair canonicity: FAIL\n\n"
        + "Candidate B Lean formalization: NOT CLAIMED\n\n"
        + "Semantic contract validity: NOT CLAIMED\n\n"
        + "Family-scale validity: NOT CLAIMED\n",
        encoding="utf-8",
    )
    return audit_result


def write_failure(out_dir: Path, failure: AuditFailure) -> None:
    clear_outputs(out_dir)
    result = {
        "schema_version": "m3-candidate-b-audit-v1",
        "overall": "FAIL",
        "failing_gate": failure.gate,
        "error": failure.message,
    }
    write_json(out_dir / "audit_result.json", result)
    (out_dir / "audit_result.md").write_text(
        "# Candidate B M3 Application Audit\n\nOverall: **FAIL**\n\n"
        "Failing gate: `%s`\n\n%s\n" % (failure.gate, failure.message),
        encoding="utf-8",
    )


def parse_args(argv: Sequence[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--contract", type=Path, required=True)
    parser.add_argument("--case-schema", type=Path, required=True)
    parser.add_argument("--source-artifacts", type=Path, required=True)
    parser.add_argument("--evidence", type=Path, required=True)
    parser.add_argument("--theorem-binding", type=Path, required=True)
    parser.add_argument("--out", type=Path, required=True)
    parser.add_argument("--repo-root", type=Path, default=Path.cwd())
    parser.add_argument(
        "--verify-source-commit",
        action="store_true",
        help=(
            "also verify evidence paths against the off-main source commit; "
            "the committed package remains replayable when that Git object is absent"
        ),
    )
    return parser.parse_args(argv)


def main(argv: Sequence[str] = ()) -> int:
    args = parse_args(argv or sys.argv[1:])
    try:
        result = validate_package(
            args.contract,
            args.case_schema,
            args.source_artifacts,
            args.evidence,
            args.theorem_binding,
            args.out,
            args.repo_root,
            verify_git_source=args.verify_source_commit,
        )
    except AuditFailure as failure:
        write_failure(args.out, failure)
        print("FAIL [%s]: %s" % (failure.gate, failure.message), file=sys.stderr)
        return 1
    print("PASS: %s" % result["claim"])
    print("Evidence mode: %s" % result["evidence_mode"])
    print("Raw repair canonicity: FAIL")
    print("Artifact-defined grouped correctness: PASS")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
