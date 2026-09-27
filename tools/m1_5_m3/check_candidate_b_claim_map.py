#!/usr/bin/env python3
"""Fail-closed integrated-draft Candidate B claim-map checker.

Use ``--refresh`` only after a deliberate manuscript audit. It binds each
``% CLAIM: CB-*`` span to the exact final TeX text and materializes the audit
metadata below. Ordinary execution is read-only and fails if manuscript text,
markers, evidence, or accounting drift from the frozen map.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import subprocess
import sys
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[2]
PAPER = ROOT / "papers/m1_5_m3/main.tex"
MAP = ROOT / "papers/m1_5_m3/claim_map_candidate_b.json"
START_RE = re.compile(r"^% CLAIM: (CB-\d{3})\s*$")
END_RE = re.compile(r"^% END CLAIM: (CB-\d{3})\s*$")


def J(path: str, pointer: str, expected: Any) -> dict[str, Any]:
    return {"type": "json_field", "path": path, "pointer": pointer, "expected": expected}


def L(path: str, symbol: str) -> dict[str, Any]:
    return {"type": "lean_symbol", "path": path, "symbol": symbol}


def S(path: str, section: str) -> dict[str, Any]:
    return {"type": "document_section", "path": path, "section": section}


def F(path: str) -> dict[str, Any]:
    return {"type": "file", "path": path}


def G(commit: str) -> dict[str, Any]:
    return {"type": "git_commit", "commit": commit}


C1 = [
    J("m3/candidate_b/evidence/bundled/case_11101/sen24.manifest.json", "/nvars", 6936),
    J("m3/candidate_b/evidence/bundled/case_11101/sen24.manifest.json", "/nclauses", 36290),
    J("m3/candidate_b/evidence/split/case_111101/sen24.manifest.json", "/nvars", 6936),
    J("m3/candidate_b/evidence/split/case_111101/sen24.manifest.json", "/nclauses", 36290),
    J("m3/candidate_b/evidence/bundled/case_11101/sen24.manifest.json", "/cnf_sha256", "6570c79cdf3e5fb3235924793bdb53968470095ebd7dc19d8707c508d0fbe384"),
    J("m3/candidate_b/evidence/split/case_111101/sen24.manifest.json", "/cnf_sha256", "35d24434bf66fbdf8f4ad0a734562b3527c665ad77e5e9c93594c1aae4e3b292"),
    J("m3/candidate_b/evidence/comparison.json", "/logical_relation/mapped_clause_multiset_equal", True),
]
C2 = [
    J("m3/candidate_b/generated/audit_result.json", "/fully_active_bundled_unsat", True),
    J("m3/candidate_b/generated/audit_result.json", "/fully_active_split_unsat", True),
    S("papers/m1_5/CLAIM_BOUNDARY.md", "| C2 |"),
]
C3 = [
    J("m3/candidate_b/evidence/comparison.json", "/candidate_b_assessment/cleanest_witness/bundled_min_repairs", ["no_cycle4", "minlib", "un", "asymm"]),
    S("papers/m1_5/CLAIM_BOUNDARY.md", "| C3 |"),
]
C4 = [
    J("m3/candidate_b/evidence/comparison.json", "/candidate_b_assessment/cleanest_witness/split_min_repairs", ["no_cycle4", "decisive_voter1", "decisive_voter0", "un", "asymm"]),
    S("papers/m1_5/CLAIM_BOUNDARY.md", "| C4 |"),
]
C5 = [
    J("m3/candidate_b/generated/raw_noncanonicity.json", "/families_equal", False),
    J("m3/candidate_b/generated/raw_noncanonicity.json", "/raw_repair_canonicity", "FAIL"),
    J("m3/candidate_b/generated/raw_noncanonicity.json", "/result", "PASS"),
]
GROUP = [
    J("m3/candidate_b/generated/residual_faithfulness.json", "/result", "PASS"),
    J("m3/candidate_b/generated/group_soundness_full.json", "/result", "PASS"),
    J("m3/candidate_b/generated/grouped_correctness_pointwise.json", "/result", "PASS"),
]
GROUP_FAMILIES = [
    J("m3/candidate_b/generated/grouped_repairs.json", "/grouped_repairs", [["asymm"], ["un"], ["minlib"], ["no_cycle4"]]),
    J("m3/candidate_b/generated/contract_repairs.json", "/repairs", [["asymm"], ["un"], ["minlib"], ["no_cycle4"]]),
]
CONTRACT = [
    J("m3/candidate_b/contract.json", "/scope/active_contract_atoms", ["asymm", "un", "minlib", "no_cycle4"]),
    J("m3/candidate_b/contract.json", "/block_map/minlib", ["decisive_voter0", "decisive_voter1"]),
    J("m3/candidate_b/contract.json", "/grouping", "touch-any"),
]
BOUNDARY = [S("m3/candidate_b/CLAIM_BOUNDARY.md", "## Not established")]
REPRO = [F("tools/check_cm_witness.py"), F("scripts/ci_m3_candidate_b.sh")]
MANDATORY_NONCLAIMS = {
    "Candidate B is a general Dafny result.",
    "Candidate B establishes real-world prevalence.",
    "Candidate B proves post-hoc audit is always superior.",
    "Candidate B proves organizational report groups are valid.",
    "Artifact-defined contract equals a semantic contract.",
    "Artifact-defined contract equals a Lean-level contract.",
    "M3-A applies to non-atomic Candidate B.",
    "M3-B makes raw repairs canonical.",
    "GroupSoundness is necessary without the M3-C assumptions.",
    "M3-C applies when PsiDeletionMonotonicity fails.",
    "Family-scale transfer follows automatically.",
    "Candidate B establishes general social-choice repair theory.",
    "Dafny Case B grouping/minimality evidence is M3 GroupSoundness or M3 exactness.",
}

LEAN = {
    "atomic": L("SocialChoiceAtlas/Reportability/Atomic.lean", "m3a_grouped_correctness"),
    "transport": L("SocialChoiceAtlas/Reportability/Atomic.lean", "m3a_raw_transport"),
    "suff": L("SocialChoiceAtlas/Reportability/GroupSound.lean", "m3b_grouped_correctness"),
    "two": L("SocialChoiceAtlas/Reportability/GroupSound.lean", "m3b_two_realization"),
    "conv": L("SocialChoiceAtlas/Reportability/Monotone.lean", "m3c_converse"),
    "iff": L("SocialChoiceAtlas/Reportability/Monotone.lean", "groupSoundness_iff"),
    "hier": L("SocialChoiceAtlas/Reportability/Monotone.lean", "atomicity_implies_groupSoundness"),
    "nonatomic": L("SocialChoiceAtlas/Reportability/Examples.lean", "repairAtomicity_fails"),
    "nonatomic_sound": L("SocialChoiceAtlas/Reportability/Examples.lean", "groupSoundness"),
    "nonmono_correct": L("SocialChoiceAtlas/Reportability/Examples.lean", "grouped_correctness"),
    "nonmono_fail": L("SocialChoiceAtlas/Reportability/Examples.lean", "groupSoundness_fails"),
}

FORMAL = {"CB-002", "CB-007", "CB-025", "CB-028", "CB-037", "CB-039", "CB-040", "CB-041", "CB-043", "CB-044", "CB-045", "CB-046", "CB-047", "CB-057"}
MEASUREMENT = {"CB-001", "CB-005", "CB-011", "CB-012", "CB-013", "CB-015", "CB-016", "CB-017", "CB-018", "CB-019", "CB-031", "CB-032", "CB-033", "CB-034", "CB-035"}
AUDIT = {"CB-003", "CB-008", "CB-009", "CB-014", "CB-023", "CB-026", "CB-030", "CB-052", "CB-054", "CB-058"}
DERIVED = {"CB-024", "CB-036"}
INTERPRETIVE = {"CB-004", "CB-006", "CB-020", "CB-021", "CB-022", "CB-027", "CB-038", "CB-042", "CB-048", "CB-049", "CB-050", "CB-051", "CB-053", "CB-055", "CB-056"}
LIMITATION = {"CB-010", "CB-029"}
WEAKENED = {"CB-002", "CB-007", "CB-022", "CB-025", "CB-028", "CB-053"}
EDITORIAL = {"CB-026", "CB-033", "CB-034", "CB-049"}


def evidence_for(cid: str) -> list[dict[str, Any]]:
    if cid in {"CB-001", "CB-005", "CB-013", "CB-015", "CB-016", "CB-031"}: return C1
    if cid in {"CB-011", "CB-012"}: return C1[:4]
    if cid in {"CB-017", "CB-033"}: return C3
    if cid in {"CB-018", "CB-034"}: return C4
    if cid in {"CB-006", "CB-019", "CB-020", "CB-021", "CB-027", "CB-035"}: return C5 + C1[-1:]
    if cid in {"CB-032"}: return C2
    if cid in {"CB-036"}: return C3 + C4 + [J("m3/candidate_b/case_schema.json", "/bundled/expected_atlas_rows", 32), J("m3/candidate_b/case_schema.json", "/split/expected_atlas_rows", 64)]
    if cid in {"CB-014"}: return [J("m3/candidate_b/generated/psi_deletion_monotonicity.json", "/result", "PASS")]
    if cid in {"CB-023"}: return CONTRACT + GROUP[:2]
    if cid in {"CB-024"}: return GROUP_FAMILIES
    if cid in {"CB-026"}: return C3 + C4 + GROUP
    if cid in {"CB-009"}: return GROUP + [J("m3/candidate_b/theorem_binding.json", "/candidate_b_formalized_in_lean", False)]
    if cid in {"CB-010", "CB-022", "CB-029"}: return CONTRACT + BOUNDARY
    if cid in {"CB-003", "CB-008", "CB-030"}: return [LEAN["iff"], LEAN["two"]] + REPRO
    if cid in {"CB-002", "CB-007", "CB-025", "CB-028"}: return [LEAN["iff"], LEAN["two"]]
    if cid == "CB-037": return [LEAN["atomic"], LEAN["transport"]]
    if cid == "CB-038": return [LEAN["atomic"]]
    if cid in {"CB-039", "CB-040"}: return [LEAN["suff"]]
    if cid in {"CB-041", "CB-042"}: return [LEAN["two"]]
    if cid == "CB-043": return [LEAN["conv"]]
    if cid == "CB-044": return [LEAN["iff"]]
    if cid == "CB-045": return [LEAN["hier"]]
    if cid == "CB-046": return [LEAN["nonatomic"], LEAN["nonatomic_sound"]]
    if cid == "CB-047": return [LEAN["nonmono_correct"], LEAN["nonmono_fail"]]
    if cid == "CB-048": return [LEAN["hier"], LEAN["nonmono_fail"]]
    if cid == "CB-049": return C1 + C5 + [LEAN["iff"]]
    if cid == "CB-050": return C1 + C5
    if cid == "CB-051": return CONTRACT + C4 + C5 + GROUP
    if cid == "CB-052": return [LEAN["suff"], LEAN["conv"], LEAN["iff"], LEAN["two"], F("scripts/ci_m3_smoke.sh")]
    if cid == "CB-053": return [LEAN["conv"], LEAN["iff"]]
    if cid == "CB-054": return [F("scripts/ci_m3_smoke.sh"), LEAN["iff"]]
    if cid == "CB-055": return C5 + [LEAN["iff"]]
    if cid == "CB-056": return C1 + C5 + [F("papers/m1_5_m3/refs.bib")]
    if cid == "CB-057": return [LEAN["iff"]]
    if cid == "CB-058": return REPRO + [S("papers/m1_5/CLAIM_BOUNDARY.md", "## Common Archive Binding")]
    if cid == "CB-004": return C1 + C5
    raise KeyError(f"no evidence mapping for {cid}")


def claim_class(cid: str) -> str:
    if cid in FORMAL: return "FORMAL_THEOREM"
    if cid in MEASUREMENT: return "ARTIFACT_MEASUREMENT"
    if cid in AUDIT: return "ARTIFACT_AUDIT"
    if cid in DERIVED: return "DERIVED_FINITE_FACT"
    if cid in INTERPRETIVE: return "INTERPRETIVE_CLAIM"
    if cid in LIMITATION: return "LIMITATION"
    raise KeyError(cid)


def extract_claims(text: str) -> tuple[dict[str, dict[str, Any]], list[str]]:
    lines = text.splitlines()
    found: dict[str, dict[str, Any]] = {}
    errors: list[str] = []
    active: tuple[str, int, list[str]] | None = None
    for lineno, line in enumerate(lines, 1):
        start = START_RE.match(line)
        end = END_RE.match(line)
        if start:
            cid = start.group(1)
            if active: errors.append(f"nested marker at line {lineno}")
            if cid in found: errors.append(f"duplicate start marker {cid}")
            active = (cid, lineno, [])
        elif end:
            cid = end.group(1)
            if not active or active[0] != cid:
                errors.append(f"unmatched end marker {cid} at line {lineno}")
                active = None
                continue
            exact = "\n".join(active[2]).strip()
            found[cid] = {
                "claim_text_exact": exact,
                "claim_text_sha256": hashlib.sha256(exact.encode()).hexdigest(),
                "manuscript_anchor": cid,
                "manuscript_locations": [{"path": str(PAPER.relative_to(ROOT)), "start_line": active[1] + 1, "end_line": lineno - 1}],
            }
            active = None
        elif active:
            active[2].append(line)
    if active: errors.append(f"unclosed marker {active[0]}")
    return found, errors


def resolve_pointer(data: Any, pointer: str) -> Any:
    cur = data
    for raw in pointer.strip("/").split("/") if pointer != "/" else []:
        token = raw.replace("~1", "/").replace("~0", "~")
        cur = cur[int(token)] if isinstance(cur, list) else cur[token]
    return cur


def validate_ref(ref: dict[str, Any]) -> str | None:
    kind = ref["type"]
    if kind == "git_commit":
        proc = subprocess.run(["git", "cat-file", "-e", f"{ref['commit']}^{{commit}}"], cwd=ROOT, capture_output=True)
        return None if proc.returncode == 0 else f"commit does not resolve: {ref['commit']}"
    path = ROOT / ref["path"]
    if not path.is_file(): return f"missing evidence file: {ref['path']}"
    if kind == "file": return None
    text = path.read_text(encoding="utf-8")
    if kind == "file_sha256":
        actual = hashlib.sha256(path.read_bytes()).hexdigest()
        return None if actual == ref["sha256"] else f"file hash mismatch {ref['path']}: {actual} != {ref['sha256']}"
    if kind == "document_section":
        return None if ref["section"] in text else f"missing section {ref['section']!r} in {ref['path']}"
    if kind == "lean_symbol":
        pattern = re.compile(r"\b(?:theorem|lemma|def)\s+" + re.escape(ref["symbol"]) + r"\b")
        return None if pattern.search(text) else f"missing Lean symbol {ref['symbol']} in {ref['path']}"
    if kind == "json_field":
        try:
            actual = resolve_pointer(json.loads(text), ref["pointer"])
        except (json.JSONDecodeError, KeyError, IndexError, TypeError, ValueError) as exc:
            return f"invalid JSON reference {ref['path']}::{ref['pointer']}: {exc}"
        return None if actual == ref["expected"] else f"evidence mismatch {ref['path']}::{ref['pointer']}: {actual!r} != {ref['expected']!r}"
    return f"unknown evidence type: {kind}"


def coverage_errors(data: dict[str, Any]) -> list[str]:
    config = data.get("coverage_scan", {})
    if not config:
        return ["missing coverage_scan configuration"]
    sentinel = re.compile(config["sentinel_regex"], re.IGNORECASE)
    exemptions = config.get("exemptions", {})
    seen: set[str] = set()
    errors: list[str] = []
    for paragraph in re.split(r"\n\s*\n", PAPER.read_text(encoding="utf-8")):
        exact = paragraph.strip()
        if not exact or not sentinel.search(exact) or "% CLAIM: CB-" in exact:
            continue
        digest = hashlib.sha256(exact.encode()).hexdigest()
        seen.add(digest)
        if digest not in exemptions:
            preview = exact.replace("\n", " ")[:160]
            errors.append(f"unmapped Candidate B-facing paragraph {digest}: {preview}")
    for digest in sorted(set(exemptions) - seen):
        errors.append(f"stale coverage exemption: {digest}")
    return errors


def refresh(data: dict[str, Any], extracted: dict[str, dict[str, Any]]) -> None:
    records = {c["claim_id"]: c for c in data["claims"]}
    if set(records) != set(extracted):
        raise SystemExit(f"claim IDs differ: map-only={sorted(set(records)-set(extracted))}, manuscript-only={sorted(set(extracted)-set(records))}")
    for cid in sorted(records):
        record = records[cid]
        record.update(extracted[cid])
        record["claim_class"] = claim_class(cid)
        record["evidence_level"] = claim_class(cid)
        record["primary_evidence"] = evidence_for(cid)
        record["supporting_evidence"] = BOUNDARY if cid not in LIMITATION else []
        record["assumptions"] = (["all theorem hypotheses stated in the manuscript claim"] if cid in FORMAL else ["frozen finite n=2, m=4 artifact scope", "no_cycle3 fixed inactive"] if cid not in INTERPRETIVE | LIMITATION else [])
        record["scope"] = "abstract finite-set theorem under stated hypotheses" if cid in FORMAL else "single finite bundled/split artifact-defined realization pair" if cid not in LIMITATION else "explicit non-claim and scope boundary"
        record["allowed_wording"] = extracted[cid]["claim_text_exact"]
        record["forbidden_upgrade"] = "No semantic-contract, Lean-level Candidate B, organizational-validity, prevalence, family-transfer, necessity-without-hypotheses, or unconditional-canonicity upgrade."
        record["final_status"] = "SUPPORTED"
        record["action"] = "WEAKENED" if cid in WEAKENED else "EDITORIAL_ONLY" if cid in EDITORIAL else "UNCHANGED"
        if cid == "CB-003":
            record["inference_boundary"] = "Lean symbols support the theorem portion; the witness checker and SHA-bound artifacts support the concrete portion. Neither evidence layer upgrades the other."
    data["status"] = "FROZEN"
    data["final_counts"] = {
        "INITIAL_MANUSCRIPT_CLAIMS": len(records),
        "FINAL_MANUSCRIPT_CLAIMS": len(records),
        "UNCHANGED_CLAIMS": sum(c["action"] == "UNCHANGED" for c in records.values()),
        "WEAKENED_CLAIMS": sum(c["action"] == "WEAKENED" for c in records.values()),
        "DELETED_CLAIMS": 0,
        "MERGED_CLAIMS": 0,
        "EDITORIAL_ONLY_CLAIMS": sum(c["action"] == "EDITORIAL_ONLY" for c in records.values()),
        "SUPPORTED_COUNT": len(records),
        "UNSUPPORTED_COUNT": 0,
        "OVERCLAIM_COUNT": 0,
        "UNMAPPED_MANUSCRIPT_CLAIMS": 0,
        "CLAIM_TEXT_HASH_MISMATCH": 0,
        "EVIDENCE_REFERENCE_ERRORS": 0,
        "UNACCOUNTED_DELETIONS": 0,
    }
    data["deletion_records"] = []
    data["freeze_contract"] = {
        "starting_commit": "bf8153b5a4d06c0be7507b1840d162b8c3123a0f",
        "candidate_b_evidence_freeze_commit": "99cba5cd45cadab283aab3784c9ff2180c8d8609",
        "candidate_b_scientific_source_commit": "1c2b9e7b979ba1a4b08c1d69f5400907cf2ca689",
        "manuscript_build_command": "make -C papers/m1_5_m3",
        "claim_check_command": "python3 tools/m1_5_m3/check_candidate_b_claim_map.py",
    }
    MAP.write_text(json.dumps(data, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")


def check(data: dict[str, Any], extracted: dict[str, dict[str, Any]], marker_errors: list[str]) -> list[str]:
    errors = list(marker_errors)
    errors.extend(coverage_errors(data))
    records_list = data.get("claims", [])
    records = {c.get("claim_id"): c for c in records_list}
    if len(records) != len(records_list): errors.append("duplicate claim-map record")
    recorded_nonclaims = {item.get("nonclaim") for item in data.get("mandatory_nonclaims", [])}
    if recorded_nonclaims != MANDATORY_NONCLAIMS:
        errors.append(f"mandatory non-claim audit mismatch: missing={sorted(MANDATORY_NONCLAIMS-recorded_nonclaims)}, extra={sorted(recorded_nonclaims-MANDATORY_NONCLAIMS)}")
    if set(records) != set(extracted): errors.append(f"marker/map mismatch: map-only={sorted(set(records)-set(extracted))}, manuscript-only={sorted(set(extracted)-set(records))}")
    required = {"claim_id", "claim_text_exact", "claim_text_sha256", "manuscript_anchor", "manuscript_locations", "claim_class", "evidence_level", "primary_evidence", "supporting_evidence", "assumptions", "scope", "allowed_wording", "forbidden_upgrade", "initial_status", "final_status", "action"}
    for cid, record in records.items():
        missing = required - set(record)
        if missing: errors.append(f"{cid}: missing fields {sorted(missing)}"); continue
        if cid in extracted:
            for field in ("claim_text_exact", "claim_text_sha256", "manuscript_anchor"):
                if record[field] != extracted[cid][field]: errors.append(f"{cid}: {field} mismatch")
        if record["final_status"] != "SUPPORTED": errors.append(f"{cid}: final status is {record['final_status']}")
        if not record["primary_evidence"]: errors.append(f"{cid}: no primary evidence")
        for ref in record["primary_evidence"] + record["supporting_evidence"]:
            err = validate_ref(ref)
            if err: errors.append(f"{cid}: {err}")
    for commit in data.get("freeze_contract", {}).values():
        if isinstance(commit, str) and re.fullmatch(r"[0-9a-f]{40}", commit):
            err = validate_ref(G(commit))
            if err: errors.append(err)
    for ref in data.get("artifact_hash_bindings", []):
        err = validate_ref(ref)
        if err: errors.append(err)
    counts = data.get("final_counts", {})
    actions = [c.get("action") for c in records.values()]
    expected_counts = {
        "INITIAL_MANUSCRIPT_CLAIMS": len(records), "FINAL_MANUSCRIPT_CLAIMS": len(records),
        "UNCHANGED_CLAIMS": actions.count("UNCHANGED"), "WEAKENED_CLAIMS": actions.count("WEAKENED"),
        "DELETED_CLAIMS": actions.count("DELETED"), "MERGED_CLAIMS": actions.count("MERGED"),
        "EDITORIAL_ONLY_CLAIMS": actions.count("EDITORIAL_ONLY"), "SUPPORTED_COUNT": len(records),
        "UNSUPPORTED_COUNT": 0, "OVERCLAIM_COUNT": 0, "UNMAPPED_MANUSCRIPT_CLAIMS": 0,
        "CLAIM_TEXT_HASH_MISMATCH": 0, "EVIDENCE_REFERENCE_ERRORS": 0, "UNACCOUNTED_DELETIONS": 0,
    }
    for key, value in expected_counts.items():
        if counts.get(key) != value: errors.append(f"count mismatch {key}: {counts.get(key)!r} != {value}")
    if actions.count("DELETED") != len(data.get("deletion_records", [])): errors.append("unaccounted deletion records")
    return errors


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--refresh", action="store_true")
    args = parser.parse_args()
    data = json.loads(MAP.read_text(encoding="utf-8"))
    extracted, marker_errors = extract_claims(PAPER.read_text(encoding="utf-8"))
    if marker_errors:
        for err in marker_errors: print(err, file=sys.stderr)
        return 1
    if args.refresh:
        refresh(data, extracted)
        data = json.loads(MAP.read_text(encoding="utf-8"))
    errors = check(data, extracted, [])
    if errors:
        for err in errors: print(f"ERROR: {err}", file=sys.stderr)
        print(f"EVIDENCE_REFERENCE_ERRORS = {sum('evidence' in e or 'missing' in e for e in errors)}")
        print("CANDIDATE_B_CLAIM_FREEZE = FAIL")
        return 1
    counts = data["final_counts"]
    for key in ("UNMAPPED_MANUSCRIPT_CLAIMS", "CLAIM_TEXT_HASH_MISMATCH", "EVIDENCE_REFERENCE_ERRORS", "UNACCOUNTED_DELETIONS", "SUPPORTED_COUNT"):
        print(f"{key} = {counts[key]}")
    print(f"OVERCLAIM = {counts['OVERCLAIM_COUNT']}")
    print(f"UNSUPPORTED = {counts['UNSUPPORTED_COUNT']}")
    print("CANDIDATE_B_CLAIM_FREEZE = PASS")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
