#!/usr/bin/env python3
from __future__ import annotations

import argparse
import hashlib
import itertools
import json
import re
import shlex
import subprocess
import sys
import time
from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

SCRIPT_DIR = Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

from gen_dimacs import run_generation  # noqa: E402
from run_atlas import _build_solver_cmd, _collect_runtime_metadata, _extract_status  # noqa: E402


@dataclass
class OracleStats:
    checks_total: int = 0
    cache_hits: int = 0
    cache_misses: int = 0
    sat_checks: int = 0
    unsat_checks: int = 0


def _load_json(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


def _write_json(path: Path, payload: dict[str, Any]) -> None:
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def _sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def _sanitize_path_string(value: Any) -> str:
    text = str(value).strip() if value is not None else ""
    if not text or text == "unknown":
        return "unknown"
    if text.startswith("/") or re.match(r"^[A-Za-z]:\\", text):
        return "<absolute>/" + Path(text).name
    return text


def _normalize_cases(atlas: dict[str, Any]) -> list[dict[str, Any]]:
    raw = atlas.get("cases", [])
    if isinstance(raw, list):
        return [c for c in raw if isinstance(c, dict)]
    if isinstance(raw, dict):
        return [c for c in raw.values() if isinstance(c, dict)]
    return []


def _mask_to_bits(mask: int, width: int) -> str:
    return "".join("1" if ((mask >> i) & 1) else "0" for i in range(width))


def _mask_to_axioms(mask: int, axiom_universe: list[str]) -> list[str]:
    return [axiom_universe[i] for i in range(len(axiom_universe)) if (mask >> i) & 1]


def _normalize_axiom_sets(raw: Any) -> list[tuple[str, ...]]:
    normalized: set[tuple[str, ...]] = set()
    if not isinstance(raw, list):
        return []
    for entry in raw:
        axioms_raw: Any
        if isinstance(entry, dict):
            axioms_raw = entry.get("remove_axioms", entry.get("removed_axioms", []))
        else:
            axioms_raw = entry
        if not isinstance(axioms_raw, list):
            continue
        axioms = tuple(sorted({str(a) for a in axioms_raw}))
        normalized.add(axioms)
    return sorted(normalized)


def _ensure_no_abs_paths(text: str) -> None:
    if "/Users/" in text:
        raise RuntimeError("output contains disallowed '/Users/' absolute path fragment")
    if re.search(r"[A-Za-z]:\\", text):
        raise RuntimeError("output contains disallowed Windows absolute path")


class StatusOracle:
    def __init__(
        self,
        *,
        solver: str,
        solver_template: str | None,
        axiom_universe: list[str],
        tmp_dir: Path,
    ) -> None:
        self.solver = solver
        self.solver_template = solver_template
        self.axiom_universe = axiom_universe
        self.tmp_dir = tmp_dir
        self.tmp_dir.mkdir(parents=True, exist_ok=True)
        self.cache: dict[int, str] = {}
        self.stats = OracleStats()

    def check_mask(self, mask: int) -> str:
        self.stats.checks_total += 1
        if mask in self.cache:
            self.stats.cache_hits += 1
            status = self.cache[mask]
            if status == "SAT":
                self.stats.sat_checks += 1
            else:
                self.stats.unsat_checks += 1
            return status

        self.stats.cache_misses += 1
        width = len(self.axiom_universe)
        bits = _mask_to_bits(mask, width)
        case_dir = self.tmp_dir / f"mask_{bits}"
        case_dir.mkdir(parents=True, exist_ok=True)
        cnf_path = case_dir / "sen24.cnf"
        manifest_path = case_dir / "sen24.manifest.json"
        model_path = case_dir / "model.txt"
        proof_path = case_dir / "proof.lrat"
        log_path = case_dir / "solver.log"

        run_generation(
            n=2,
            m=4,
            axiom_names=_mask_to_axioms(mask, self.axiom_universe),
            out_path=cnf_path,
            manifest_path=manifest_path,
        )
        cmd = _build_solver_cmd(
            solver=self.solver,
            solver_template=self.solver_template,
            cnf_path=cnf_path,
            proof_path=proof_path,
            model_path=model_path,
            with_proof=False,
        )

        t0 = time.perf_counter()
        try:
            proc = subprocess.run(cmd, capture_output=True, text=True, check=False)
            duration = time.perf_counter() - t0
            status = _extract_status(f"{proc.stdout}\n{proc.stderr}", proc.returncode)
            lines = [
                "command: " + " ".join(shlex.quote(x) for x in cmd),
                f"return_code: {proc.returncode}",
                f"duration_sec: {duration:.6f}",
                "----- STDOUT -----",
                proc.stdout.rstrip("\n"),
                "----- STDERR -----",
                proc.stderr.rstrip("\n"),
            ]
            log_path.write_text("\n".join(lines).rstrip() + "\n", encoding="utf-8")
        except FileNotFoundError as ex:
            raise RuntimeError(f"solver command not found: {cmd[0]}") from ex

        if status not in {"SAT", "UNSAT"}:
            raise RuntimeError(
                f"triangulation solver returned non-decisive status '{status}' for mask {bits}; "
                f"see {log_path}"
            )

        self.cache[mask] = status
        if status == "SAT":
            self.stats.sat_checks += 1
        else:
            self.stats.unsat_checks += 1
        return status


def _resolve_backend(requested: str) -> tuple[str, str | None]:
    if requested == "bruteforce":
        return "bruteforce", None
    if requested in {"auto", "pysat_rc2"}:
        try:
            __import__("pysat")
        except Exception:
            return "bruteforce", "python-sat unavailable; fallback to bruteforce"
        return "bruteforce", "pysat_rc2 backend not enabled in this minimal profile; fallback to bruteforce"
    raise ValueError(f"unknown backend: {requested}")


def _compute_optimum_repairs(
    *,
    unsat_mask: int,
    axiom_universe: list[str],
    oracle: StatusOracle,
) -> tuple[int, list[tuple[str, ...]]]:
    width = len(axiom_universe)
    on_indices = [i for i in range(width) if (unsat_mask >> i) & 1]
    for size in range(1, len(on_indices) + 1):
        winners: list[tuple[str, ...]] = []
        for combo in itertools.combinations(on_indices, size):
            remove_mask = 0
            for idx in combo:
                remove_mask |= 1 << idx
            trial_mask = unsat_mask & ~remove_mask
            status = oracle.check_mask(trial_mask)
            if status == "SAT":
                winners.append(tuple(sorted(axiom_universe[i] for i in combo)))
        if winners:
            return size, sorted(set(winners))
    raise RuntimeError(f"no SAT repair found for UNSAT mask {unsat_mask}")


def main() -> None:
    ap = argparse.ArgumentParser(description="Triangulate MCS minima against an independent optimum baseline")
    ap.add_argument("--atlas-outdir", type=Path, required=True, help="Atlas output directory containing atlas.json")
    ap.add_argument(
        "--outdir",
        type=Path,
        default=None,
        help="Output directory for triangulation artifacts (default: atlas-outdir)",
    )
    ap.add_argument("--solver", type=str, default="cadical")
    ap.add_argument("--solver-template", type=str, default=None)
    ap.add_argument("--backend", choices=["auto", "bruteforce", "pysat_rc2"], default="auto")
    ap.add_argument(
        "--tmp-dir",
        type=Path,
        default=None,
        help="Temporary directory for solver runs (default: <outdir>/triangulation_tmp)",
    )
    args = ap.parse_args()

    atlas_path = args.atlas_outdir / "atlas.json"
    if not atlas_path.exists():
        raise FileNotFoundError(f"missing atlas.json: {atlas_path}")
    atlas_raw = atlas_path.read_bytes()
    atlas = json.loads(atlas_raw.decode("utf-8"))

    schema_version = atlas.get("atlas_schema_version")
    if not isinstance(schema_version, int) or schema_version < 1:
        raise ValueError("atlas_schema_version missing or invalid")
    cases = _normalize_cases(atlas)
    if int(atlas.get("cases_total", len(cases))) != len(cases):
        raise ValueError("atlas cases_total does not match number of cases")

    outdir = args.outdir if args.outdir is not None else args.atlas_outdir
    outdir.mkdir(parents=True, exist_ok=True)
    tmp_dir = args.tmp_dir if args.tmp_dir is not None else outdir / "triangulation_tmp"

    axiom_universe = list(atlas.get("axiom_universe", []))
    if not axiom_universe:
        raise ValueError("atlas axiom_universe is missing or empty")

    unsat_cases = [
        c
        for c in sorted(cases, key=lambda x: str(x.get("case_id", "")))
        if str(c.get("status", "UNKNOWN")) == "UNSAT" and bool(c.get("solved", False))
    ]
    if not unsat_cases:
        raise RuntimeError("no solved UNSAT cases found in atlas for triangulation")
    for case in unsat_cases:
        if case.get("mcs_min_size") is None or case.get("mcs_min_all") is None:
            raise RuntimeError(
                f"case {case.get('case_id')} is missing mcs_min_size/mcs_min_all; run enumerate_repairs first"
            )

    backend_used, backend_note = _resolve_backend(args.backend)
    oracle = StatusOracle(
        solver=args.solver,
        solver_template=args.solver_template,
        axiom_universe=axiom_universe,
        tmp_dir=tmp_dir,
    )

    entries: list[dict[str, Any]] = []
    for case in unsat_cases:
        case_id = str(case["case_id"])
        unsat_mask = int(case["mask_int"])
        optimum_drop_count, optimum_repairs = _compute_optimum_repairs(
            unsat_mask=unsat_mask,
            axiom_universe=axiom_universe,
            oracle=oracle,
        )

        mcs_min_size = int(case.get("mcs_min_size"))
        mcs_min_all = _normalize_axiom_sets(case.get("mcs_min_all"))
        optimum_norm = sorted(set(optimum_repairs))
        size_match = optimum_drop_count == mcs_min_size
        set_match = set(optimum_norm) == set(mcs_min_all)

        entry = {
            "case_id": case_id,
            "axioms_on": list(case.get("axioms_on", [])),
            "optimum_drop_count": optimum_drop_count,
            "optimum_repairs": [list(x) for x in optimum_norm],
            "compare": {
                "mcs_min_size": mcs_min_size,
                "mcs_min_all": [list(x) for x in mcs_min_all],
                "size_match": size_match,
                "set_match": set_match,
            },
            "verdict": "match" if (size_match and set_match) else "mismatch",
        }
        entries.append(entry)

    runtime_meta = _collect_runtime_metadata(args.solver)
    solver_info = dict(runtime_meta.get("solver_info", {}))
    solver_info["solver_path"] = _sanitize_path_string(solver_info.get("solver_path"))
    solver_info["solver_version_raw"] = str(solver_info.get("solver_version_raw", "unknown"))
    solver_info["solver_version"] = str(solver_info.get("solver_version", "unknown"))
    solver_info["solver_sha256"] = str(solver_info.get("solver_sha256", "unknown"))

    report = {
        "triangulation_schema_version": 1,
        "generated_at_utc": datetime.now(timezone.utc).isoformat(),
        "backend_requested": args.backend,
        "backend_used": backend_used,
        "backend_note": backend_note,
        "atlas_schema_version": schema_version,
        "atlas_sha256": _sha256_bytes(atlas_raw),
        "solver_info": solver_info,
        "reproduce": {
            "command": (
                "python3 scripts/triangulate_repairs.py "
                "--atlas-outdir <atlas_outdir> --outdir <outdir> "
                f"--backend {args.backend} --solver {args.solver}"
            )
        },
        "oracle_stats": {
            "checks_total": oracle.stats.checks_total,
            "cache_hits": oracle.stats.cache_hits,
            "cache_misses": oracle.stats.cache_misses,
            "sat_checks": oracle.stats.sat_checks,
            "unsat_checks": oracle.stats.unsat_checks,
            "cache_size": len(oracle.cache),
        },
        "cases": entries,
    }

    report_json_path = outdir / "repair_triangulation.json"
    report_md_path = outdir / "repair_triangulation.md"
    _write_json(report_json_path, report)

    md_lines: list[str] = []
    md_lines.append("# Repair Triangulation")
    md_lines.append("")
    md_lines.append(
        "This report compares enumerated `mcs_min_size`/`mcs_min_all` with an independent optimum baseline "
        "(bruteforce solver checks over axiom-drop subsets)."
    )
    md_lines.append("")
    md_lines.append("| case_id | optimum_drop_count | mcs_min_size | size_match | set_match |")
    md_lines.append("|---|---:|---:|---:|---:|")
    for entry in entries:
        compare = entry["compare"]
        md_lines.append(
            f"| `{entry['case_id']}` | {entry['optimum_drop_count']} | {compare['mcs_min_size']} | "
            f"{compare['size_match']} | {compare['set_match']} |"
        )
    md_lines.append("")
    for entry in entries:
        md_lines.append(f"## {entry['case_id']}")
        md_lines.append("")
        md_lines.append(f"- axioms_on: `{', '.join(entry['axioms_on'])}`")
        md_lines.append(f"- optimum_repairs: `{entry['optimum_repairs']}`")
        md_lines.append(f"- mcs_min_all: `{entry['compare']['mcs_min_all']}`")
        md_lines.append(
            f"- verdict: `size_match={entry['compare']['size_match']}`, "
            f"`set_match={entry['compare']['set_match']}`"
        )
        md_lines.append("")
    report_md = "\n".join(md_lines).rstrip() + "\n"
    _ensure_no_abs_paths(report_json_path.read_text(encoding="utf-8"))
    _ensure_no_abs_paths(report_md)
    report_md_path.write_text(report_md, encoding="utf-8")

    print(f"Wrote {report_json_path}")
    print(f"Wrote {report_md_path}")


if __name__ == "__main__":
    main()
