#!/usr/bin/env python3
from __future__ import annotations

import argparse
import itertools
import json
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
from run_atlas import _build_solver_cmd, _extract_status  # noqa: E402


@dataclass
class OracleStats:
    checks_total: int = 0
    cache_hits: int = 0
    cache_misses: int = 0
    sat_checks: int = 0
    unsat_checks: int = 0
    unknown_checks: int = 0


def _mask_to_axioms(mask: int, axiom_universe: list[str]) -> list[str]:
    return [axiom_universe[i] for i in range(len(axiom_universe)) if (mask >> i) & 1]


def _mask_to_bits(mask: int, width: int) -> str:
    return "".join("1" if ((mask >> i) & 1) else "0" for i in range(width))


def _parse_case_ids(raw: str | None) -> set[str] | None:
    if raw is None:
        return None
    ids = {x.strip() for x in raw.split(",") if x.strip()}
    return ids if ids else None


def _parse_bool_status(status: str) -> str:
    if status in {"SAT", "UNSAT", "UNKNOWN"}:
        return status
    return "UNKNOWN"


def _write_solver_log(path: Path, *, cmd: list[str], return_code: int | None, stdout: str, stderr: str, duration_sec: float, error: str | None = None) -> None:
    lines = [
        "command: " + " ".join(shlex.quote(x) for x in cmd),
        f"return_code: {return_code}",
        f"duration_sec: {duration_sec:.6f}",
    ]
    if error is not None:
        lines.append(f"error: {error}")
    lines.append("----- STDOUT -----")
    lines.append(stdout.rstrip("\n"))
    lines.append("----- STDERR -----")
    lines.append(stderr.rstrip("\n"))
    path.write_text("\n".join(lines).rstrip() + "\n", encoding="utf-8")


class SatOracle:
    def __init__(
        self,
        *,
        axiom_universe: list[str],
        solver: str,
        solver_template: str | None,
        tmp_dir: Path,
        emit_proof: bool,
    ) -> None:
        self.axiom_universe = axiom_universe
        self.solver = solver
        self.solver_template = solver_template
        self.tmp_dir = tmp_dir
        self.emit_proof = emit_proof
        self.cache: dict[int, str] = {}
        self.stats = OracleStats()
        self.tmp_dir.mkdir(parents=True, exist_ok=True)

    def preload(self, atlas_cases: list[dict[str, Any]]) -> None:
        for case in atlas_cases:
            try:
                mask = int(case["mask_int"])
                status = _parse_bool_status(str(case.get("status", "UNKNOWN")))
            except Exception:
                continue
            if status in {"SAT", "UNSAT"}:
                self.cache[mask] = status

    def check_mask(self, mask: int) -> str:
        self.stats.checks_total += 1
        if mask in self.cache:
            self.stats.cache_hits += 1
            status = self.cache[mask]
            if status == "SAT":
                self.stats.sat_checks += 1
            elif status == "UNSAT":
                self.stats.unsat_checks += 1
            else:
                self.stats.unknown_checks += 1
            return status

        self.stats.cache_misses += 1
        width = len(self.axiom_universe)
        bits = _mask_to_bits(mask, width)
        case_tmp = self.tmp_dir / f"mask_{bits}"
        case_tmp.mkdir(parents=True, exist_ok=True)
        cnf_path = case_tmp / "sen24.cnf"
        manifest_path = case_tmp / "sen24.manifest.json"
        proof_path = case_tmp / "proof.lrat"
        model_path = case_tmp / "model.txt"
        log_path = case_tmp / "solver.log"

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
            with_proof=self.emit_proof,
        )
        t0 = time.perf_counter()
        try:
            proc = subprocess.run(cmd, capture_output=True, text=True, check=False)
            duration = time.perf_counter() - t0
            status = _extract_status(f"{proc.stdout}\n{proc.stderr}", proc.returncode)
            status = _parse_bool_status(status)
            _write_solver_log(
                log_path,
                cmd=cmd,
                return_code=proc.returncode,
                stdout=proc.stdout,
                stderr=proc.stderr,
                duration_sec=duration,
            )
        except FileNotFoundError as ex:
            duration = time.perf_counter() - t0
            status = "UNKNOWN"
            _write_solver_log(
                log_path,
                cmd=cmd,
                return_code=None,
                stdout="",
                stderr="",
                duration_sec=duration,
                error=str(ex),
            )

        self.cache[mask] = status
        if status == "SAT":
            self.stats.sat_checks += 1
        elif status == "UNSAT":
            self.stats.unsat_checks += 1
        else:
            self.stats.unknown_checks += 1
        return status


def compute_mus(mask_unsat: int, axiom_universe: list[str], oracle: SatOracle) -> dict[str, Any]:
    start = time.perf_counter()
    initial_status = oracle.check_mask(mask_unsat)
    if initial_status != "UNSAT":
        return {
            "status": "skipped",
            "reason": f"initial status is {initial_status}, not UNSAT",
            "method": "deletion_v1",
            "initial_mask": mask_unsat,
            "initial_axioms": _mask_to_axioms(mask_unsat, axiom_universe),
            "time_ms": int((time.perf_counter() - start) * 1000),
        }

    width = len(axiom_universe)
    current = mask_unsat
    unknown_hits = 0
    removal_trace: list[dict[str, Any]] = []

    for i, ax in enumerate(axiom_universe):
        if not ((current >> i) & 1):
            continue
        trial = current & ~(1 << i)
        status = oracle.check_mask(trial)
        removal_trace.append(
            {
                "drop_axiom": ax,
                "trial_mask": trial,
                "trial_bits": _mask_to_bits(trial, width),
                "status": status,
            }
        )
        if status == "UNSAT":
            current = trial
        elif status == "UNKNOWN":
            unknown_hits += 1

    minimal_verified = True
    for i in range(width):
        if not ((current >> i) & 1):
            continue
        trial = current & ~(1 << i)
        status = oracle.check_mask(trial)
        if status == "UNSAT":
            minimal_verified = False
            break
        if status == "UNKNOWN":
            minimal_verified = False

    mus_axioms = _mask_to_axioms(current, axiom_universe)
    return {
        "status": "ok",
        "method": "deletion_v1",
        "initial_mask": mask_unsat,
        "initial_bits": _mask_to_bits(mask_unsat, width),
        "initial_axioms": _mask_to_axioms(mask_unsat, axiom_universe),
        "mus_mask": current,
        "mus_bits": _mask_to_bits(current, width),
        "mus_axioms": mus_axioms,
        "size": len(mus_axioms),
        "unknown_hits": unknown_hits,
        "minimal_verified": minimal_verified,
        "time_ms": int((time.perf_counter() - start) * 1000),
        "trace": removal_trace,
    }


def compute_mcs(mask_unsat: int, axiom_universe: list[str], oracle: SatOracle, *, max_pair_trials: int) -> dict[str, Any]:
    start = time.perf_counter()
    width = len(axiom_universe)
    if oracle.check_mask(mask_unsat) != "UNSAT":
        return {
            "status": "skipped",
            "reason": "initial set is not UNSAT",
            "method": "small_mcs_v1",
            "time_ms": int((time.perf_counter() - start) * 1000),
        }

    present = [i for i in range(width) if (mask_unsat >> i) & 1]
    trials = 0

    for i in present:
        trial_mask = mask_unsat & ~(1 << i)
        status = oracle.check_mask(trial_mask)
        trials += 1
        if status == "SAT":
            removed = [axiom_universe[i]]
            return {
                "status": "ok",
                "method": "single_then_pairs_v1",
                "size": 1,
                "removed_axioms": removed,
                "removed_mask_bits": _mask_to_bits(mask_unsat ^ trial_mask, width),
                "sat_mask": trial_mask,
                "sat_bits": _mask_to_bits(trial_mask, width),
                "trials": trials,
                "time_ms": int((time.perf_counter() - start) * 1000),
            }

    pair_trials = 0
    for i, j in itertools.combinations(present, 2):
        if pair_trials >= max_pair_trials:
            break
        trial_mask = mask_unsat & ~(1 << i) & ~(1 << j)
        status = oracle.check_mask(trial_mask)
        trials += 1
        pair_trials += 1
        if status == "SAT":
            removed = [axiom_universe[i], axiom_universe[j]]
            return {
                "status": "ok",
                "method": "single_then_pairs_v1",
                "size": 2,
                "removed_axioms": removed,
                "removed_mask_bits": _mask_to_bits(mask_unsat ^ trial_mask, width),
                "sat_mask": trial_mask,
                "sat_bits": _mask_to_bits(trial_mask, width),
                "trials": trials,
                "pair_trials": pair_trials,
                "time_ms": int((time.perf_counter() - start) * 1000),
            }

    return {
        "status": "not_found",
        "method": "single_then_pairs_v1",
        "max_pair_trials": max_pair_trials,
        "trials": trials,
        "pair_trials": pair_trials,
        "time_ms": int((time.perf_counter() - start) * 1000),
    }


def resolve_atlas_path(*, atlas: Path | None, outdir: Path | None) -> Path:
    if atlas is not None and outdir is not None:
        atlas_from_outdir = outdir / "atlas.json"
        if atlas.resolve() != atlas_from_outdir.resolve():
            raise ValueError("Provide either --atlas or --outdir, or both pointing to the same atlas.")
        return atlas
    if atlas is not None:
        return atlas
    if outdir is not None:
        return outdir / "atlas.json"
    raise ValueError("One of --atlas or --outdir is required.")


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--atlas", type=Path, default=None, help="Path to atlas.json")
    ap.add_argument("--outdir", type=Path, default=None, help="Atlas directory containing atlas.json")
    ap.add_argument("--solver", type=str, default="cadical")
    ap.add_argument("--solver-template", type=str, default=None)
    ap.add_argument(
        "--tmp-dir",
        type=Path,
        default=None,
        help="Temporary working directory for SAT checks (default: <outdir>/mus_tmp).",
    )
    ap.add_argument("--emit-proof", action="store_true")
    ap.add_argument("--max-unsat-cases", type=int, default=None)
    ap.add_argument("--case-ids", type=str, default=None, help="Comma-separated case IDs to process.")
    ap.add_argument("--max-pair-trials", type=int, default=20)
    ap.add_argument("--atlas-out", type=Path, default=None, help="Output atlas path (default: overwrite input)")
    args = ap.parse_args()

    atlas_path = resolve_atlas_path(atlas=args.atlas, outdir=args.outdir)
    outdir = args.outdir if args.outdir is not None else atlas_path.parent
    atlas_obj = json.loads(atlas_path.read_text(encoding="utf-8"))
    axiom_universe = list(atlas_obj["axiom_universe"])
    if len(axiom_universe) != 5:
        raise ValueError(f"Expected 5-axiom universe for sen24 week2, got {len(axiom_universe)}")

    case_filter = _parse_case_ids(args.case_ids)

    all_cases: list[dict[str, Any]] = list(atlas_obj.get("cases", []))
    target_cases = []
    skipped_unsolved: list[str] = []
    for case in all_cases:
        status = str(case.get("status", "UNKNOWN"))
        if status != "UNSAT":
            continue
        if not bool(case.get("solved", True)):
            skipped_unsolved.append(str(case.get("case_id", "")))
            continue
        cid = str(case.get("case_id", ""))
        if case_filter is not None and cid not in case_filter:
            continue
        target_cases.append(case)

    if args.max_unsat_cases is not None:
        target_cases = target_cases[: args.max_unsat_cases]

    if not target_cases:
        detail = ""
        if skipped_unsolved:
            detail = (
                " (all UNSAT candidates are inferred/pruned with solved=false; "
                "re-run run_atlas.py with --prune none or include a solved UNSAT case)"
            )
        raise RuntimeError(f"No UNSAT solved cases selected for MUS/MCS extraction.{detail}")

    tmp_dir = args.tmp_dir if args.tmp_dir is not None else outdir / "mus_tmp"
    oracle = SatOracle(
        axiom_universe=axiom_universe,
        solver=args.solver,
        solver_template=args.solver_template,
        tmp_dir=tmp_dir,
        emit_proof=args.emit_proof,
    )
    oracle.preload(all_cases)

    processed = 0
    for case in target_cases:
        mask = int(case["mask_int"])
        case_id = str(case["case_id"])
        case_dir = outdir / case_id
        case_dir.mkdir(parents=True, exist_ok=True)

        mus = compute_mus(mask, axiom_universe, oracle)
        mcs = compute_mcs(mask, axiom_universe, oracle, max_pair_trials=args.max_pair_trials)

        case["mus"] = mus
        case["mcs"] = mcs

        (case_dir / "mus.json").write_text(json.dumps(mus, indent=2, sort_keys=True) + "\n", encoding="utf-8")
        (case_dir / "mcs.json").write_text(json.dumps(mcs, indent=2, sort_keys=True) + "\n", encoding="utf-8")
        summary_path = case_dir / "summary.json"
        if summary_path.exists():
            summary_obj = json.loads(summary_path.read_text(encoding="utf-8"))
            summary_obj["mus"] = mus
            summary_obj["mcs"] = mcs
            summary_path.write_text(json.dumps(summary_obj, indent=2, sort_keys=True) + "\n", encoding="utf-8")
        processed += 1

    atlas_obj["mus_mcs"] = {
        "generated_at_utc": datetime.now(timezone.utc).isoformat(),
        "solver": args.solver,
        "solver_template": args.solver_template,
        "tmp_dir": str(tmp_dir),
        "processed_unsat_cases": processed,
        "max_unsat_cases": args.max_unsat_cases,
        "case_ids_filter": sorted(case_filter) if case_filter is not None else None,
        "oracle_stats": {
            "checks_total": oracle.stats.checks_total,
            "cache_hits": oracle.stats.cache_hits,
            "cache_misses": oracle.stats.cache_misses,
            "sat_checks": oracle.stats.sat_checks,
            "unsat_checks": oracle.stats.unsat_checks,
            "unknown_checks": oracle.stats.unknown_checks,
            "cache_size": len(oracle.cache),
        },
        "max_pair_trials": args.max_pair_trials,
    }

    output_atlas = args.atlas_out if args.atlas_out is not None else atlas_path
    output_atlas.write_text(json.dumps(atlas_obj, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(f"Wrote {output_atlas}")


if __name__ == "__main__":
    main()
