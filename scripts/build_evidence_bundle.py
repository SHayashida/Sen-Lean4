#!/usr/bin/env python3
from __future__ import annotations

import argparse
import hashlib
import json
import platform as py_platform
import re
import shlex
import shutil
import subprocess
import sys
import time
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

SCRIPT_DIR = Path(__file__).resolve().parent
REPO_ROOT = SCRIPT_DIR.parent

RUN_ATLAS = SCRIPT_DIR / "run_atlas.py"
MUS_MCS = SCRIPT_DIR / "mus_mcs.py"
ENUMERATE_REPAIRS = SCRIPT_DIR / "enumerate_repairs.py"
BUILD_SAT_GALLERY = SCRIPT_DIR / "build_sat_gallery.py"
PLOT_FRONTIER = SCRIPT_DIR / "plot_frontier.py"
PLOT_HASSE = SCRIPT_DIR / "plot_hasse_frontier.py"
TRIANGULATE = SCRIPT_DIR / "triangulate_repairs.py"
MAXSAT_BASELINE = SCRIPT_DIR / "maxsat_baseline.py"
SUMMARIZE_ATLAS = SCRIPT_DIR / "summarize_atlas.py"
GEN_PAPER_TABLES = SCRIPT_DIR / "gen_paper_tables.py"

BUNDLE_SCHEMA_VERSION = 1
DETERMINISTIC_TIME = "1970-01-01T00:00:00+00:00"
VOLATILE_TIME_KEYS = {"generated_at_utc", "generated_utc"}
VOLATILE_FLOAT_KEYS = {"duration_sec", "wall_time_sec"}


def _load_json(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


def _write_json(path: Path, payload: dict[str, Any]) -> None:
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def _sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as f:
        for chunk in iter(lambda: f.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def _normalize_cases(atlas: dict[str, Any]) -> list[dict[str, Any]]:
    raw = atlas.get("cases", [])
    if isinstance(raw, list):
        return [c for c in raw if isinstance(c, dict)]
    if isinstance(raw, dict):
        return [c for c in raw.values() if isinstance(c, dict)]
    return []


def _probe_git_commit() -> str:
    try:
        proc = subprocess.run(
            ["git", "rev-parse", "HEAD"],
            cwd=str(REPO_ROOT),
            capture_output=True,
            text=True,
            check=False,
            timeout=5.0,
        )
    except (FileNotFoundError, subprocess.TimeoutExpired):
        return "unknown"
    if proc.returncode != 0:
        return "unknown"
    commit = proc.stdout.strip()
    return commit if commit else "unknown"


def _sanitize_path(value: Any) -> str:
    text = str(value).strip() if value is not None else ""
    if not text:
        return "unknown"
    if text == "unknown":
        return text
    if text.startswith("/") or re.match(r"^[A-Za-z]:\\", text):
        return f"<absolute>/{Path(text).name}"
    return text


def _ensure_public_safe_text(path: Path) -> None:
    text = path.read_text(encoding="utf-8", errors="ignore")
    if "/Users/" in text:
        raise RuntimeError(f"path leak '/Users/' detected in {path}")
    if re.search(r"[A-Za-z]:\\", text):
        raise RuntimeError(f"Windows absolute path leak detected in {path}")


def _normalize_text_for_determinism(text: str, *, bundle_outdir: Path, atlas_outdir: Path) -> str:
    normalized = text.replace(str(bundle_outdir), "<bundle_outdir>")
    normalized = normalized.replace(str(atlas_outdir), "<bundle_outdir>/atlas")
    normalized = normalized.replace(str(REPO_ROOT), "<repo_root>")
    if normalized.startswith("/Users/"):
        return "<redacted-home>/" + Path(normalized).name
    if re.match(r"^[A-Za-z]:\\", normalized):
        return "<absolute>/" + Path(normalized).name
    return normalized


def _normalize_json_for_determinism(
    value: Any,
    *,
    parent_key: str | None,
    bundle_outdir: Path,
    atlas_outdir: Path,
) -> Any:
    if isinstance(value, dict):
        out: dict[str, Any] = {}
        for key in sorted(value.keys()):
            raw = value[key]
            if key in VOLATILE_TIME_KEYS:
                out[key] = DETERMINISTIC_TIME
                continue
            if key == "atlas_sha256":
                out[key] = "<deterministic_atlas_sha256>"
                continue
            if key in VOLATILE_FLOAT_KEYS:
                out[key] = 0.0
                continue
            out[key] = _normalize_json_for_determinism(
                raw,
                parent_key=key,
                bundle_outdir=bundle_outdir,
                atlas_outdir=atlas_outdir,
            )
        return out
    if isinstance(value, list):
        return [
            _normalize_json_for_determinism(
                x,
                parent_key=parent_key,
                bundle_outdir=bundle_outdir,
                atlas_outdir=atlas_outdir,
            )
            for x in value
        ]
    if isinstance(value, float) and parent_key in VOLATILE_FLOAT_KEYS:
        return 0.0
    if isinstance(value, str):
        return _normalize_text_for_determinism(value, bundle_outdir=bundle_outdir, atlas_outdir=atlas_outdir)
    return value


def _canonicalize_bundle_json_outputs(*, bundle_outdir: Path, atlas_outdir: Path) -> None:
    json_paths = sorted(p for p in bundle_outdir.rglob("*.json") if p.name != "bundle.json")
    for path in json_paths:
        try:
            payload = json.loads(path.read_text(encoding="utf-8"))
        except json.JSONDecodeError:
            continue
        normalized = _normalize_json_for_determinism(
            payload,
            parent_key=None,
            bundle_outdir=bundle_outdir,
            atlas_outdir=atlas_outdir,
        )
        path.write_text(json.dumps(normalized, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def _scan_bundle_for_path_leaks(root: Path) -> list[str]:
    suspicious: list[str] = []
    text_suffixes = {".json", ".md", ".tex", ".csv", ".dot"}
    for path in sorted(p for p in root.rglob("*") if p.is_file() and p.suffix.lower() in text_suffixes):
        text = path.read_text(encoding="utf-8", errors="ignore")
        if "/Users/" in text or re.search(r"[A-Za-z]:\\", text):
            suspicious.append(path.relative_to(root).as_posix())
    return suspicious


def _tiny_case_masks() -> list[int]:
    return [mask for mask in range(32) if (mask & (1 << 3)) == 0]


def _format_cmd_for_manifest(cmd: list[str], bundle_outdir: Path, atlas_outdir: Path) -> str:
    rendered: list[str] = []
    bundle_token = str(bundle_outdir)
    atlas_token = str(atlas_outdir)
    for tok in cmd:
        value = tok
        value = value.replace(bundle_token, "<bundle_outdir>")
        value = value.replace(atlas_token, "<bundle_outdir>/atlas")
        if value.startswith("/Users/"):
            value = "<redacted-home>/" + Path(value).name
        if re.match(r"^[A-Za-z]:\\", value):
            value = "<absolute>/" + Path(value).name
        rendered.append(value)
    return " ".join(shlex.quote(x) for x in rendered)


def _run_step(
    *,
    name: str,
    cmd: list[str],
    logs_dir: Path,
    bundle_outdir: Path,
    atlas_outdir: Path,
) -> dict[str, Any]:
    log_path = logs_dir / f"{name}.log"
    t0 = time.perf_counter()
    proc = subprocess.run(cmd, cwd=str(REPO_ROOT), capture_output=True, text=True, check=False)
    duration = time.perf_counter() - t0
    rendered_cmd = _format_cmd_for_manifest(cmd, bundle_outdir, atlas_outdir)
    lines = [
        "command: " + rendered_cmd,
        f"return_code: {proc.returncode}",
        f"duration_sec: {duration:.6f}",
        "----- STDOUT -----",
        proc.stdout.rstrip("\n"),
        "----- STDERR -----",
        proc.stderr.rstrip("\n"),
    ]
    log_path.write_text("\n".join(lines).rstrip() + "\n", encoding="utf-8")
    if proc.returncode != 0:
        raise RuntimeError(f"step '{name}' failed; see {log_path}")
    return {
        "name": name,
        "status": "ok",
        "duration_sec": duration,
        "return_code": proc.returncode,
        "command": rendered_cmd,
        "log": log_path.relative_to(bundle_outdir).as_posix(),
    }


def _collect_artifacts(root: Path) -> list[dict[str, Any]]:
    include_suffixes = {".json", ".md", ".tex", ".csv", ".dot", ".cnf"}
    files = sorted(
        p
        for p in root.rglob("*")
        if p.is_file() and p.name != "bundle.json" and p.suffix.lower() in include_suffixes
    )
    rows: list[dict[str, Any]] = []
    for path in files:
        rel = path.relative_to(root).as_posix()
        rows.append(
            {
                "path": rel,
                "size_bytes": path.stat().st_size,
                "sha256": _sha256_file(path),
            }
        )
    return rows


def _build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description="Build a deterministic evidence bundle for claims C1-C6")
    parser.add_argument("--outdir", type=Path, required=True, help="Bundle output root directory")
    parser.add_argument("--mode", choices=["tiny", "full"], default="tiny")
    parser.add_argument("--solver", type=str, default="cadical")
    parser.add_argument("--jobs", type=int, default=1)
    parser.add_argument("--symmetry", choices=["none", "alts"], default="none")
    parser.add_argument("--prune", choices=["none", "monotone"], default="none")
    parser.add_argument(
        "--deterministic",
        dest="deterministic",
        action="store_true",
        help="Enable deterministic bundle normalization (default: ON for tiny mode).",
    )
    parser.add_argument(
        "--no-deterministic",
        dest="deterministic",
        action="store_false",
        help="Disable deterministic bundle normalization.",
    )
    parser.set_defaults(deterministic=None)
    parser.add_argument("--dry-run", action="store_true")
    return parser


def main() -> None:
    args = _build_parser().parse_args()
    if args.jobs < 1:
        raise ValueError("--jobs must be >= 1")

    deterministic = args.deterministic if args.deterministic is not None else (args.mode == "tiny")

    bundle_outdir = args.outdir
    atlas_outdir = bundle_outdir / "atlas"
    paper_fig_outdir = bundle_outdir / "paper" / "figures" / "generated"
    paper_table_outdir = bundle_outdir / "paper" / "tables" / "generated"
    logs_dir = bundle_outdir / "logs"

    if bundle_outdir.exists():
        shutil.rmtree(bundle_outdir)
    paper_fig_outdir.mkdir(parents=True, exist_ok=True)
    paper_table_outdir.mkdir(parents=True, exist_ok=True)
    logs_dir.mkdir(parents=True, exist_ok=True)

    case_masks = _tiny_case_masks() if args.mode == "tiny" else None
    steps: list[dict[str, Any]] = []
    skipped_steps: list[dict[str, Any]] = []

    if args.dry_run:
        run_atlas_cmd = [
            sys.executable,
            str(RUN_ATLAS),
            "--outdir",
            str(atlas_outdir),
            "--solver",
            args.solver,
            "--jobs",
            str(args.jobs),
            "--prune",
            args.prune,
            "--symmetry",
            args.symmetry,
            "--emit-proof",
            "unsat-only",
        ]
        if case_masks is not None:
            run_atlas_cmd.extend(["--case-masks", ",".join(str(m) for m in case_masks)])
        print(_format_cmd_for_manifest(run_atlas_cmd, bundle_outdir, atlas_outdir))
        return

    run_atlas_cmd = [
        sys.executable,
        str(RUN_ATLAS),
        "--outdir",
        str(atlas_outdir),
        "--solver",
        args.solver,
        "--jobs",
        str(args.jobs),
        "--prune",
        args.prune,
        "--symmetry",
        args.symmetry,
        "--emit-proof",
        "unsat-only",
    ]
    if args.symmetry == "alts":
        run_atlas_cmd.append("--symmetry-check")
    if args.prune == "monotone":
        run_atlas_cmd.append("--prune-check")
    if case_masks is not None:
        run_atlas_cmd.extend(["--case-masks", ",".join(str(m) for m in case_masks)])
    steps.append(
        _run_step(
            name="01_run_atlas",
            cmd=run_atlas_cmd,
            logs_dir=logs_dir,
            bundle_outdir=bundle_outdir,
            atlas_outdir=atlas_outdir,
        )
    )

    atlas_path = atlas_outdir / "atlas.json"
    if not atlas_path.exists():
        raise FileNotFoundError(f"missing atlas.json after run_atlas: {atlas_path}")
    atlas = _load_json(atlas_path)
    cases = _normalize_cases(atlas)
    unsat_cases = [c for c in cases if str(c.get("status", "UNKNOWN")) == "UNSAT"]
    solved_unsat_cases = [c for c in unsat_cases if bool(c.get("solved", False))]
    can_enumerate_repairs = bool(unsat_cases) and len(unsat_cases) == len(solved_unsat_cases)
    baseline_case_id: str | None = None
    solved_unsat_ids = sorted(str(c.get("case_id", "")) for c in solved_unsat_cases)
    if "case_11111" in solved_unsat_ids:
        baseline_case_id = "case_11111"
    elif solved_unsat_ids:
        baseline_case_id = solved_unsat_ids[0]

    if solved_unsat_cases:
        steps.append(
            _run_step(
                name="02_mus_mcs",
                cmd=[
                    sys.executable,
                    str(MUS_MCS),
                    "--outdir",
                    str(atlas_outdir),
                    "--solver",
                    args.solver,
                    "--max-pair-trials",
                    "20",
                ],
                logs_dir=logs_dir,
                bundle_outdir=bundle_outdir,
                atlas_outdir=atlas_outdir,
            )
        )
    else:
        skipped_steps.append(
            {
                "name": "02_mus_mcs",
                "status": "skipped",
                "reason": "no solved UNSAT cases",
            }
        )

    if can_enumerate_repairs:
        steps.append(
            _run_step(
                name="03_enumerate_repairs",
                cmd=[sys.executable, str(ENUMERATE_REPAIRS), "--outdir", str(atlas_outdir)],
                logs_dir=logs_dir,
                bundle_outdir=bundle_outdir,
                atlas_outdir=atlas_outdir,
            )
        )
    else:
        skipped_steps.append(
            {
                "name": "03_enumerate_repairs",
                "status": "skipped",
                "reason": "UNSAT set contains solved=false entries",
            }
        )

    top_k = 3 if args.mode == "tiny" else 5
    steps.append(
        _run_step(
            name="04_build_sat_gallery",
            cmd=[
                sys.executable,
                str(BUILD_SAT_GALLERY),
                "--atlas-outdir",
                str(atlas_outdir),
                "--top-k",
                str(top_k),
                "--min-k",
                "1",
            ],
            logs_dir=logs_dir,
            bundle_outdir=bundle_outdir,
            atlas_outdir=atlas_outdir,
        )
    )

    steps.append(
        _run_step(
            name="05_plot_frontier",
            cmd=[
                sys.executable,
                str(PLOT_FRONTIER),
                "--atlas-outdir",
                str(atlas_outdir),
                "--outdir",
                str(paper_fig_outdir),
                "--format",
                "png",
            ],
            logs_dir=logs_dir,
            bundle_outdir=bundle_outdir,
            atlas_outdir=atlas_outdir,
        )
    )
    steps.append(
        _run_step(
            name="06_plot_hasse",
            cmd=[
                sys.executable,
                str(PLOT_HASSE),
                "--atlas-outdir",
                str(atlas_outdir),
                "--outdir",
                str(paper_fig_outdir),
                "--format",
                "png",
                "--include-pruned",
                "false" if args.prune == "none" else "true",
                "--show",
                "status",
            ],
            logs_dir=logs_dir,
            bundle_outdir=bundle_outdir,
            atlas_outdir=atlas_outdir,
        )
    )

    repair_enumeration_done = (atlas_outdir / "atlas.json").exists() and can_enumerate_repairs
    if repair_enumeration_done:
        steps.append(
            _run_step(
                name="07_triangulate_repairs",
                cmd=[
                    sys.executable,
                    str(TRIANGULATE),
                    "--atlas-outdir",
                    str(atlas_outdir),
                    "--outdir",
                    str(atlas_outdir),
                    "--backend",
                    "bruteforce",
                    "--solver",
                    args.solver,
                ],
                logs_dir=logs_dir,
                bundle_outdir=bundle_outdir,
                atlas_outdir=atlas_outdir,
            )
        )
    else:
        skipped_steps.append(
            {
                "name": "07_triangulate_repairs",
                "status": "skipped",
                "reason": "triangulation requires enumerate_repairs outputs",
            }
        )

    if baseline_case_id is not None:
        steps.append(
            _run_step(
                name="08_maxsat_baseline",
                cmd=[
                    sys.executable,
                    str(MAXSAT_BASELINE),
                    "--atlas-outdir",
                    str(atlas_outdir),
                    "--case-id",
                    baseline_case_id,
                    "--solver",
                    args.solver,
                ],
                logs_dir=logs_dir,
                bundle_outdir=bundle_outdir,
                atlas_outdir=atlas_outdir,
            )
        )
    else:
        skipped_steps.append(
            {
                "name": "08_maxsat_baseline",
                "status": "skipped",
                "reason": "no solved UNSAT case available",
            }
        )

    steps.append(
        _run_step(
            name="09_summarize_atlas",
            cmd=[sys.executable, str(SUMMARIZE_ATLAS), "--outdir", str(atlas_outdir)],
            logs_dir=logs_dir,
            bundle_outdir=bundle_outdir,
            atlas_outdir=atlas_outdir,
        )
    )
    steps.append(
        _run_step(
            name="10_gen_paper_tables",
            cmd=[
                sys.executable,
                str(GEN_PAPER_TABLES),
                "--atlas-outdir",
                str(atlas_outdir),
                "--outdir",
                str(paper_table_outdir),
            ],
            logs_dir=logs_dir,
            bundle_outdir=bundle_outdir,
            atlas_outdir=atlas_outdir,
        )
    )

    if deterministic:
        _canonicalize_bundle_json_outputs(bundle_outdir=bundle_outdir, atlas_outdir=atlas_outdir)

    atlas = _load_json(atlas_outdir / "atlas.json")
    gallery = _load_json(atlas_outdir / "gallery.json")
    non_trivial_validated = sum(
        1
        for entry in gallery.get("entries", [])
        if isinstance(entry, dict) and bool(entry.get("non_trivial")) and bool(entry.get("model_validated"))
    )
    if non_trivial_validated < 1:
        raise RuntimeError("bundle requires at least one validated non-trivial SAT gallery entry")

    repairs_table_path = paper_table_outdir / "repairs_table.tex"
    if not repairs_table_path.exists():
        raise RuntimeError(f"missing generated table: {repairs_table_path}")
    maxsat_baseline_path = atlas_outdir / "maxsat_baseline.json"
    if baseline_case_id is not None and not maxsat_baseline_path.exists():
        raise RuntimeError(f"missing maxsat baseline output: {maxsat_baseline_path}")

    leak_hits = _scan_bundle_for_path_leaks(bundle_outdir)
    if leak_hits:
        raise RuntimeError(f"bundle path leak check failed for files: {leak_hits}")

    for path in sorted(p for p in bundle_outdir.rglob("*") if p.is_file() and p.suffix.lower() in {".json", ".md", ".tex"}):
        _ensure_public_safe_text(path)

    solver_info = dict(atlas.get("solver_info", {}))
    environment_info = dict(atlas.get("environment_info", {}))
    commands_payload: list[dict[str, Any]] = steps + skipped_steps
    if deterministic:
        commands_payload = _normalize_json_for_determinism(
            commands_payload,
            parent_key=None,
            bundle_outdir=bundle_outdir,
            atlas_outdir=atlas_outdir,
        )

    bundle = {
        "bundle_schema_version": BUNDLE_SCHEMA_VERSION,
        "generated_at_utc": DETERMINISTIC_TIME if deterministic else datetime.now(timezone.utc).isoformat(),
        "mode": args.mode,
        "config": {
            "solver": args.solver,
            "jobs": args.jobs,
            "symmetry": args.symmetry,
            "prune": args.prune,
            "deterministic": deterministic,
            "tiny_case_masks": case_masks if args.mode == "tiny" else None,
        },
        "metadata": {
            "git_commit": environment_info.get("git_commit", _probe_git_commit()),
            "python_version": sys.version.split()[0],
            "platform": py_platform.platform(),
            "solver_info": {
                "solver_name": solver_info.get("solver_name", args.solver),
                "solver_path": _sanitize_path(solver_info.get("solver_path", "unknown")),
                "solver_version_raw": str(solver_info.get("solver_version_raw", "unknown")),
                "solver_version": str(solver_info.get("solver_version", "unknown")),
                "solver_sha256": str(solver_info.get("solver_sha256", "unknown")),
            },
        },
        "claims_coverage": {
            "C1": True,
            "C2": bool(solved_unsat_cases),
            "C3": True,
            "C4": args.symmetry == "alts" or args.prune == "monotone",
            "C5": non_trivial_validated >= 1,
            "C6": repair_enumeration_done and (baseline_case_id is not None),
        },
        "commands": commands_payload,
        "checks": {
            "path_leak_scan": {"passed": True, "checked_extensions": [".json", ".md", ".tex", ".csv", ".dot"]},
            "non_trivial_validated_entries": non_trivial_validated,
            "unsat_cases_total": len(unsat_cases),
            "unsat_cases_solved": len(solved_unsat_cases),
            "deterministic_mode": deterministic,
            "maxsat_baseline_case_id": baseline_case_id,
        },
        "artifacts": {
            "atlas_dir": "atlas",
            "paper_dir": "paper",
            "files": _collect_artifacts(bundle_outdir),
        },
        "reproduce": {
            "tiny": (
                "python3 scripts/build_evidence_bundle.py --mode tiny "
                "--outdir <bundle_outdir> --solver cadical --jobs 1 --symmetry none --prune none"
            ),
            "full": (
                "python3 scripts/build_evidence_bundle.py --mode full "
                "--outdir <bundle_outdir> --solver cadical --jobs 4 --symmetry none --prune none"
            ),
            "lean_case11111": "lake build SocialChoiceAtlas.Sen.Atlas.Case11111",
        },
    }

    bundle_path = bundle_outdir / "bundle.json"
    _write_json(bundle_path, bundle)
    _ensure_public_safe_text(bundle_path)
    print(f"Wrote {bundle_path}")


if __name__ == "__main__":
    main()
