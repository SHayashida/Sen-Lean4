#!/usr/bin/env python3
"""Rebuild the Candidate B package from curated or historical evidence."""

from __future__ import annotations

import argparse
import hashlib
import json
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path
from typing import Any, Dict, List

sys.path.insert(0, str(Path(__file__).resolve().parents[2]))

from tools.m3_candidate_b.fault_injections import run_fault_suite
from tools.m3_candidate_b.validate_candidate_b import (
    EVIDENCE_SOURCE_COMMIT,
    validate_package,
)


SOURCE_ROOT = "results/20260401/candidate_b_minlib_granularity"


def git_bytes(repo: Path, source_path: str) -> bytes:
    return subprocess.check_output(
        ["git", "show", "%s:%s" % (EVIDENCE_SOURCE_COMMIT, source_path)],
        cwd=str(repo),
    )


def git_blob(repo: Path, source_path: str) -> str:
    return subprocess.check_output(
        ["git", "rev-parse", "%s:%s" % (EVIDENCE_SOURCE_COMMIT, source_path)],
        cwd=str(repo),
        text=True,
    ).strip()


def load_source_json(repo: Path, relative: str) -> Any:
    return json.loads(git_bytes(repo, SOURCE_ROOT + "/" + relative).decode("utf-8"))


def selected_paths(repo: Path) -> List[str]:
    bundled = load_source_json(repo, "bundled/atlas.json")
    split = load_source_json(repo, "split/atlas.json")
    bundled_ids = [row["case_id"] for row in bundled["cases"] if row["mask_bits"][3] == "0"]
    split_ids = [row["case_id"] for row in split["cases"] if row["mask_bits"][4] == "0"]
    if len(bundled_ids) != 16 or len(split_ids) != 32:
        raise RuntimeError("application filter did not select 16 bundled and 32 split rows")
    paths = ["comparison.json", "bundled/atlas.json", "split/atlas.json"]
    for representation, case_ids in (("bundled", bundled_ids), ("split", split_ids)):
        for case_id in case_ids:
            paths.append("%s/%s/sen24.manifest.json" % (representation, case_id))
            paths.append("%s/%s/summary.json" % (representation, case_id))
    if len(paths) != 99:
        raise RuntimeError("curated whitelist must contain exactly 99 evidence files")
    return sorted(paths)


def write_manifest(package: Path) -> None:
    manifest = package / "MANIFEST.sha256"
    rows = []
    for path in sorted(package.rglob("*")):
        if path.is_file() and path != manifest:
            relative = path.relative_to(package).as_posix()
            rows.append("%s  %s" % (hashlib.sha256(path.read_bytes()).hexdigest(), relative))
    manifest.write_text("\n".join(rows) + "\n", encoding="utf-8")


def write_fault_report(package: Path, repo: Path) -> None:
    results = run_fault_suite(package, repo)
    if any(row["result"] != "PASS" for row in results):
        raise RuntimeError("one or more fault injections did not fail at the expected gate")
    output = {
        "schema_version": "m3-candidate-b-fault-injection-v1",
        "faults_expected": 15,
        "faults_observed": len(results),
        "all_rejected": True,
        "rows": results,
        "result": "PASS",
    }
    generated = package / "generated"
    (generated / "fault_injection_results.json").write_text(
        json.dumps(output, ensure_ascii=True, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    lines = [
        "# Fault-Injection Results",
        "",
        "| Fault | Expected gate | Observed gate | Exit | Result |",
        "|---|---|---|---:|---|",
    ]
    for row in results:
        lines.append(
            "| `%s` | `%s` | `%s` | %d | %s |"
            % (
                row["fault"], row["expected_gate"], row["observed_gate"],
                row["observed_exit_code"], row["result"],
            )
        )
    lines.extend(["", "All 15 mandatory faults were rejected at the expected gate.", ""])
    (generated / "fault_injection_results.md").write_text("\n".join(lines), encoding="utf-8")


def rebuild_historical_evidence(package: Path, repo: Path) -> None:
    evidence = package / "evidence"
    entries: List[Dict[str, str]] = []
    with tempfile.TemporaryDirectory(prefix="candidate-b-freeze-") as temporary:
        staged = Path(temporary) / "evidence"
        for relative in selected_paths(repo):
            source_path = SOURCE_ROOT + "/" + relative
            data = git_bytes(repo, source_path)
            destination = staged / relative
            destination.parent.mkdir(parents=True, exist_ok=True)
            destination.write_bytes(data)
            entries.append({
                "source_path": source_path,
                "source_blob_sha": git_blob(repo, source_path),
                "content_sha256": hashlib.sha256(data).hexdigest(),
                "package_path": "evidence/" + relative,
            })
        if evidence.exists():
            shutil.rmtree(str(evidence))
        shutil.copytree(str(staged), str(evidence))
    source = {
        "schema_version": "m3-candidate-b-source-artifacts-v1",
        "source_commit": EVIDENCE_SOURCE_COMMIT,
        "evidence_root": "m3/candidate_b/evidence",
        "whitelist_policy": "exact-paths-only",
        "entries": entries,
    }
    (package / "source_artifacts.json").write_text(
        json.dumps(source, ensure_ascii=True, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--source-mode",
        choices=("curated", "historical"),
        default="curated",
        help=(
            "curated validates the tracked self-contained evidence snapshot; "
            "historical re-extracts the same whitelist from the recorded off-main Git object"
        ),
    )
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    package = Path(__file__).resolve().parent
    repo = package.parents[1]
    evidence = package / "evidence"
    if args.source_mode == "historical":
        rebuild_historical_evidence(package, repo)
    elif not evidence.is_dir() or not (package / "source_artifacts.json").is_file():
        raise RuntimeError("curated evidence snapshot or source binding is missing")
    validate_package(
        package / "contract.json",
        package / "case_schema.json",
        package / "source_artifacts.json",
        evidence,
        package / "theorem_binding.json",
        package / "generated",
        repo,
        verify_git_source=args.source_mode == "historical",
    )
    write_fault_report(package, repo)
    write_manifest(package)
    print("PASS: built 99-file Candidate B evidence whitelist (%s mode)" % args.source_mode)
    if args.source_mode == "historical":
        print("PASS: source commit binding verified against Git history")
    else:
        print("PASS: self-contained curated source binding verified")
    print("PASS: 15 fault injections rejected")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
