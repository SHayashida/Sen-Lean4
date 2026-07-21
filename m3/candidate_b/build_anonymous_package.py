#!/usr/bin/env python3
"""Build and verify a deterministic, identity-sanitized Candidate B archive."""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import shutil
import subprocess
import sys
import tempfile
import zipfile
from pathlib import Path
from typing import Any, Dict, Iterable, List


PUBLIC_COMMITS = [
    "1c2b9e7b979ba1a4b08c1d69f5400907cf2ca689",
    "e33805d0ff0a64f12e450ba7aaa150729901d7d2",
]
WITHHELD = "WITHHELD_FOR_ANONYMOUS_REVIEW"
FIXED_ZIP_TIME = (1980, 1, 1, 0, 0, 0)


def sanitize(value: Any) -> Any:
    if isinstance(value, list):
        return [sanitize(item) for item in value]
    if isinstance(value, dict):
        result = {key: sanitize(item) for key, item in value.items()}
        for key in ("generated_at_utc", "date"):
            if key in result:
                result[key] = "withheld-for-anonymous-review"
        if "duration_sec" in result:
            result["duration_sec"] = 0.0
        return result
    return value


def write_json(path: Path, value: Any) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(
        json.dumps(value, ensure_ascii=True, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )


def git_blob_sha(data: bytes) -> str:
    return hashlib.sha1(("blob %d\0" % len(data)).encode("ascii") + data).hexdigest()


def copy_sanitized_json_tree(source: Path, destination: Path) -> None:
    for path in sorted(source.rglob("*.json")):
        relative = path.relative_to(source)
        write_json(destination / relative, sanitize(json.loads(path.read_text(encoding="utf-8"))))


def write_manifest(root: Path) -> None:
    manifest = root / "m3" / "candidate_b" / "MANIFEST.sha256"
    rows = []
    for path in sorted(root.rglob("*")):
        if path.is_file() and path != manifest:
            rows.append(
                "%s  %s"
                % (hashlib.sha256(path.read_bytes()).hexdigest(), path.relative_to(root).as_posix())
            )
    manifest.write_text("\n".join(rows) + "\n", encoding="utf-8")


def scan_identity(root: Path) -> None:
    banned = [
        "/" + "Users/", "SHayashida", "github.com", "codex/", "@openai",
    ] + PUBLIC_COMMITS
    findings: List[str] = []
    for path in sorted(root.rglob("*")):
        if not path.is_file():
            continue
        try:
            text = path.read_text(encoding="utf-8")
        except UnicodeDecodeError:
            continue
        for token in banned:
            if token.lower() in text.lower():
                findings.append("%s: %s" % (path.relative_to(root).as_posix(), token))
        if re.search(r"[A-Za-z0-9._%+-]+@[A-Za-z0-9.-]+\.[A-Za-z]{2,}", text):
            findings.append("%s: email-address pattern" % path.relative_to(root).as_posix())
        if re.search(r"\b20\d{2}-\d{2}-\d{2}(?:[T ][0-9:.+-Z]+)?\b", text):
            findings.append("%s: timestamp pattern" % path.relative_to(root).as_posix())
    if findings:
        raise RuntimeError("anonymous identity scan failed: " + "; ".join(findings))


def create_zip(root: Path, output: Path) -> None:
    output.parent.mkdir(parents=True, exist_ok=True)
    with zipfile.ZipFile(str(output), "w", compression=zipfile.ZIP_DEFLATED, compresslevel=9) as archive:
        for path in sorted(root.rglob("*")):
            if not path.is_file():
                continue
            relative = Path("candidate_b_artifact") / path.relative_to(root)
            info = zipfile.ZipInfo(relative.as_posix(), FIXED_ZIP_TIME)
            info.compress_type = zipfile.ZIP_DEFLATED
            info.external_attr = 0o100644 << 16
            archive.writestr(info, path.read_bytes())


def build(repo: Path, output: Path) -> str:
    public = repo / "m3" / "candidate_b"
    with tempfile.TemporaryDirectory(prefix="candidate-b-anonymous-") as temporary:
        root = Path(temporary) / "root"
        package = root / "m3" / "candidate_b"
        package.mkdir(parents=True)
        for name in (
            "contract.json", "case_schema.json", "environment.json",
            "CLAIM_BOUNDARY.md", "LICENSE_STATUS.md",
        ):
            shutil.copy2(str(public / name), str(package / name))
        shutil.copy2(str(public / "ANONYMOUS_README.md"), str(root / "README.md"))
        shutil.copy2(
            str(public / "verify_anonymous_manifest.py"),
            str(root / "verify_anonymous_manifest.py"),
        )
        copy_sanitized_json_tree(public / "evidence", package / "evidence")
        shutil.copytree(str(public / "generated"), str(package / "generated"))

        source_entries: List[Dict[str, str]] = []
        for path in sorted((package / "evidence").rglob("*")):
            if path.is_file():
                relative = path.relative_to(package).as_posix()
                data = path.read_bytes()
                source_entries.append({
                    "source_path": "anonymous/" + relative,
                    "source_blob_sha": git_blob_sha(data),
                    "content_sha256": hashlib.sha256(data).hexdigest(),
                    "package_path": relative,
                })
        write_json(package / "source_artifacts.json", {
            "schema_version": "m3-candidate-b-source-artifacts-v1",
            "source_commit": WITHHELD,
            "evidence_root": "m3/candidate_b/evidence",
            "whitelist_policy": "exact-paths-only",
            "entries": source_entries,
        })
        theorem = json.loads((public / "theorem_binding.json").read_text(encoding="utf-8"))
        theorem["source_commit"] = WITHHELD
        write_json(package / "theorem_binding.json", theorem)

        validator = (repo / "tools" / "m3_candidate_b" / "validate_candidate_b.py").read_text(encoding="utf-8")
        for commit in PUBLIC_COMMITS:
            validator = validator.replace(commit, WITHHELD)
        validator_path = root / "tools" / "m3_candidate_b" / "validate_candidate_b.py"
        validator_path.parent.mkdir(parents=True)
        validator_path.write_text(validator, encoding="utf-8")
        (validator_path.parent / "__init__.py").write_text("\"\"\"Anonymous validator package.\"\"\"\n", encoding="utf-8")

        for relative in (
            "SocialChoiceAtlas/Reportability/Defs.lean",
            "SocialChoiceAtlas/Reportability/GroupSound.lean",
            "SocialChoiceAtlas/Reportability/Monotone.lean",
            "SocialChoiceAtlas/Reportability/Examples.lean",
            "scripts/ci_m3_smoke.sh",
            "lean-toolchain",
        ):
            destination = root / relative
            destination.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(str(repo / relative), str(destination))

        command = [
            sys.executable, "tools/m3_candidate_b/validate_candidate_b.py",
            "--contract", "m3/candidate_b/contract.json",
            "--case-schema", "m3/candidate_b/case_schema.json",
            "--source-artifacts", "m3/candidate_b/source_artifacts.json",
            "--evidence", "m3/candidate_b/evidence",
            "--theorem-binding", "m3/candidate_b/theorem_binding.json",
            "--out", "m3/candidate_b/generated",
            "--repo-root", ".",
        ]
        subprocess.check_call(command, cwd=str(root))
        write_manifest(root)
        scan_identity(root)
        create_zip(root, output)
    digest = hashlib.sha256(output.read_bytes()).hexdigest()
    output.with_suffix(output.suffix + ".sha256").write_text(
        "%s  %s\n" % (digest, output.name), encoding="utf-8"
    )
    print("PASS: anonymous package identity scan")
    print("PASS: anonymous package validator")
    print("SHA256: " + digest)
    return digest


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=Path("/tmp/m3-candidate-b-anonymous.zip"))
    args = parser.parse_args()
    repo = Path(__file__).resolve().parents[2]
    build(repo, args.output.resolve())
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
