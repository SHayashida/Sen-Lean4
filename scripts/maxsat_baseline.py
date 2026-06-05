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
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

SCRIPT_DIR = Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

from gen_dimacs import run_generation  # noqa: E402
from run_atlas import _build_solver_cmd, _collect_runtime_metadata, _extract_status  # noqa: E402


def _load_json(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


def _write_json(path: Path, payload: dict[str, Any]) -> None:
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def _sanitize_path(text: Any) -> str:
    value = str(text).strip() if text is not None else ""
    if not value:
        return "unknown"
    if value == "unknown":
        return value
    if value.startswith("/") or re.match(r"^[A-Za-z]:\\", value):
        return "<absolute>/" + Path(value).name
    return value


def _status_from_case(case: dict[str, Any]) -> str:
    status = str(case.get("status", "UNKNOWN"))
    solved = bool(case.get("solved", False))
    if solved and status in {"SAT", "UNSAT"}:
        return status
    return "UNKNOWN"


class SatOracle:
    def __init__(
        self,
        *,
        axiom_universe: list[str],
        solver: str,
        solver_template: str | None,
        tmp_dir: Path,
    ) -> None:
        self.axiom_universe = axiom_universe
        self.solver = solver
        self.solver_template = solver_template
        self.tmp_dir = tmp_dir
        self.cache: dict[int, str] = {}
        self.stats = {
            "checks_total": 0,
            "cache_hits": 0,
            "cache_misses": 0,
            "sat_checks": 0,
            "unsat_checks": 0,
            "unknown_checks": 0,
        }
        self.tmp_dir.mkdir(parents=True, exist_ok=True)

    def preload(self, cases: list[dict[str, Any]]) -> None:
        for case in cases:
            try:
                mask = int(case.get("mask_int"))
            except Exception:
                continue
            status = _status_from_case(case)
            if status in {"SAT", "UNSAT"}:
                self.cache[mask] = status

    def _record(self, status: str) -> None:
        if status == "SAT":
            self.stats["sat_checks"] += 1
        elif status == "UNSAT":
            self.stats["unsat_checks"] += 1
        else:
            self.stats["unknown_checks"] += 1

    def check_mask(self, mask: int) -> str:
        self.stats["checks_total"] += 1
        if mask in self.cache:
            self.stats["cache_hits"] += 1
            status = self.cache[mask]
            self._record(status)
            return status

        self.stats["cache_misses"] += 1
        case_tmp = self.tmp_dir / f"mask_{mask:05b}"
        case_tmp.mkdir(parents=True, exist_ok=True)
        cnf_path = case_tmp / "sen24.cnf"
        manifest_path = case_tmp / "sen24.manifest.json"
        proof_path = case_tmp / "proof.lrat"
        model_path = case_tmp / "model.txt"
        log_path = case_tmp / "solver.log"

        axioms_on = [self.axiom_universe[i] for i in range(len(self.axiom_universe)) if (mask >> i) & 1]
        run_generation(n=2, m=4, axiom_names=axioms_on, out_path=cnf_path, manifest_path=manifest_path)
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
        except FileNotFoundError as ex:
            raise RuntimeError(f"solver not found: {cmd[0]}") from ex
        elapsed = time.perf_counter() - t0
        status = _extract_status(f"{proc.stdout}\n{proc.stderr}", proc.returncode)
        if status not in {"SAT", "UNSAT"}:
            status = "UNKNOWN"
        log_lines = [
            "command: " + " ".join(shlex.quote(x) for x in cmd),
            f"return_code: {proc.returncode}",
            f"duration_sec: {elapsed:.6f}",
            "----- STDOUT -----",
            proc.stdout.rstrip("\n"),
            "----- STDERR -----",
            proc.stderr.rstrip("\n"),
        ]
        log_path.write_text("\n".join(log_lines).rstrip() + "\n", encoding="utf-8")
        self.cache[mask] = status
        self._record(status)
        return status


def _find_min_repair(
    *,
    unsat_mask: int,
    axiom_universe: list[str],
    oracle: SatOracle,
) -> tuple[int, list[str], int]:
    on_indices = [i for i in range(len(axiom_universe)) if (unsat_mask >> i) & 1]
    if oracle.check_mask(unsat_mask) != "UNSAT":
        raise RuntimeError("target case is not UNSAT under oracle checks")

    for k in range(1, len(on_indices) + 1):
        for combo in itertools.combinations(on_indices, k):
            remove_mask = 0
            for idx in combo:
                remove_mask |= 1 << idx
            trial_mask = unsat_mask & ~remove_mask
            status = oracle.check_mask(trial_mask)
            if status == "SAT":
                one_set = [axiom_universe[i] for i in combo]
                return k, one_set, remove_mask
    raise RuntimeError("no SAT repair found by exhaustive search")


def _sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def main() -> None:
    parser = argparse.ArgumentParser(description="Tiny MAXSAT-style sanity baseline via exhaustive axiom-drop search")
    parser.add_argument("--atlas-outdir", type=Path, required=True, help="Atlas directory containing atlas.json")
    parser.add_argument("--case-id", type=str, default="case_11111", help="Target UNSAT case id")
    parser.add_argument("--solver", type=str, default="cadical")
    parser.add_argument("--solver-template", type=str, default=None)
    parser.add_argument(
        "--out",
        type=Path,
        default=None,
        help="Output JSON path (default: <atlas-outdir>/maxsat_baseline.json)",
    )
    parser.add_argument(
        "--tmp-dir",
        type=Path,
        default=None,
        help="Temporary directory for SAT checks (default: <atlas-outdir>/maxsat_tmp)",
    )
    args = parser.parse_args()

    atlas_path = args.atlas_outdir / "atlas.json"
    if not atlas_path.exists():
        raise FileNotFoundError(f"missing atlas.json: {atlas_path}")
    atlas_raw = atlas_path.read_bytes()
    atlas = json.loads(atlas_raw.decode("utf-8"))
    schema = atlas.get("atlas_schema_version")
    if not isinstance(schema, int) or schema < 1:
        raise ValueError("atlas_schema_version missing or invalid")

    cases_raw = atlas.get("cases", [])
    cases = cases_raw if isinstance(cases_raw, list) else list(cases_raw.values())
    cases = [c for c in cases if isinstance(c, dict)]
    case_map = {str(c.get("case_id", "")): c for c in cases}
    target = case_map.get(args.case_id)
    if target is None:
        raise RuntimeError(f"target case not found in atlas: {args.case_id}")
    if not bool(target.get("solved", False)):
        raise RuntimeError(f"target case must have solved=true: {args.case_id}")
    if str(target.get("status", "UNKNOWN")) != "UNSAT":
        raise RuntimeError(f"target case must be UNSAT: {args.case_id}")

    axiom_universe = list(atlas.get("axiom_universe", []))
    if not axiom_universe:
        raise ValueError("atlas axiom_universe is missing/empty")
    unsat_mask = int(target.get("mask_int"))
    tmp_dir = args.tmp_dir if args.tmp_dir is not None else args.atlas_outdir / "maxsat_tmp"
    oracle = SatOracle(
        axiom_universe=axiom_universe,
        solver=args.solver,
        solver_template=args.solver_template,
        tmp_dir=tmp_dir,
    )
    oracle.preload(cases)

    min_size, one_repair_set, remove_mask = _find_min_repair(
        unsat_mask=unsat_mask,
        axiom_universe=axiom_universe,
        oracle=oracle,
    )

    runtime_meta = _collect_runtime_metadata(args.solver)
    solver_info = dict(runtime_meta.get("solver_info", {}))
    report = {
        "schema_version": 1,
        "generated_at_utc": datetime.now(timezone.utc).isoformat(),
        "backend": "exhaustive_axiom_drop_v1",
        "atlas_schema_version": schema,
        "atlas_sha256": _sha256_bytes(atlas_raw),
        "case_id": str(target.get("case_id", "")),
        "axioms_on": list(target.get("axioms_on", [])),
        "min_repair_size": min_size,
        "one_repair_set": one_repair_set,
        "one_repair_mask_bits": f"{remove_mask:0{len(axiom_universe)}b}",
        "solver_info": {
            "solver_name": solver_info.get("solver_name", args.solver),
            "solver_path": _sanitize_path(solver_info.get("solver_path", "unknown")),
            "solver_version_raw": str(solver_info.get("solver_version_raw", "unknown")),
            "solver_version": str(solver_info.get("solver_version", "unknown")),
            "solver_sha256": str(solver_info.get("solver_sha256", "unknown")),
        },
        "oracle_stats": {
            **oracle.stats,
            "cache_size": len(oracle.cache),
        },
        "reproduce": {
            "command": (
                "python3 scripts/maxsat_baseline.py "
                "--atlas-outdir <atlas_outdir> "
                f"--case-id {args.case_id} --solver {args.solver}"
            )
        },
    }

    out_path = args.out if args.out is not None else args.atlas_outdir / "maxsat_baseline.json"
    _write_json(out_path, report)
    print(f"Wrote {out_path}")


if __name__ == "__main__":
    main()
