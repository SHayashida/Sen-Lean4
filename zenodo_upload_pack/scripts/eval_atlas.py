#!/usr/bin/env python3
from __future__ import annotations

import argparse
import csv
import hashlib
import itertools
import json
import platform as py_platform
import shlex
import shutil
import statistics
import subprocess
import sys
import time
from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

SCRIPT_DIR = Path(__file__).resolve().parent
RUN_ATLAS = SCRIPT_DIR / "run_atlas.py"
MUS_MCS = SCRIPT_DIR / "mus_mcs.py"
SUMMARIZE = SCRIPT_DIR / "summarize_atlas.py"
EVAL_SCHEMA_VERSION = 1

DEFAULT_CONFIG_IDS = ["none_none", "alts_none", "none_monotone", "alts_monotone"]
CONFIG_PRESETS = {
    "none_none": ("none", "none"),
    "alts_none": ("alts", "none"),
    "none_monotone": ("none", "monotone"),
    "alts_monotone": ("alts", "monotone"),
}
TRIVIALITY_SAMPLE_CASE_IDS = [
    "case_00000",
    "case_10000",
    "case_01000",
    "case_00100",
    "case_00010",
]


@dataclass(frozen=True)
class EvalConfig:
    config_id: str
    symmetry: str
    prune: str


@dataclass(frozen=True)
class CommandResult:
    returncode: int
    wall_time_sec: float


def _sha256_file(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as f:
        for chunk in iter(lambda: f.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def _resolve_solver_path(solver: str) -> str | None:
    found = shutil.which(solver)
    if found is not None:
        return str(Path(found).resolve())
    candidate = Path(solver)
    if candidate.exists():
        return str(candidate.resolve())
    return None


def _sanitize_solver_path(path: str | None) -> str:
    if path is None:
        return "unknown"
    normalized = str(path).strip()
    if not normalized:
        return "unknown"
    if normalized.startswith("/Users/"):
        return f"<redacted-home>/{Path(normalized).name}"
    return normalized


def _probe_git_commit() -> str:
    try:
        proc = subprocess.run(
            ["git", "rev-parse", "HEAD"],
            cwd=SCRIPT_DIR.parent,
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


def _load_json(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


def _write_json(path: Path, payload: dict[str, Any]) -> None:
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def _mean(values: list[float]) -> float:
    if not values:
        return 0.0
    return float(sum(values) / len(values))


def _stddev(values: list[float]) -> float:
    if len(values) < 2:
        return 0.0
    return float(statistics.pstdev(values))


def _parse_configs(raw: str | None) -> list[EvalConfig]:
    tokens: list[str]
    if raw is None:
        tokens = DEFAULT_CONFIG_IDS
    else:
        tokens = [tok.strip() for tok in raw.split(",") if tok.strip()]
        if not tokens:
            raise ValueError("--configs is empty")

    configs: list[EvalConfig] = []
    seen: set[str] = set()
    for token in tokens:
        if token in CONFIG_PRESETS:
            symmetry, prune = CONFIG_PRESETS[token]
            config_id = token
        elif ":" in token:
            symmetry, prune = [part.strip() for part in token.split(":", 1)]
            if symmetry not in {"none", "alts"}:
                raise ValueError(f"invalid symmetry in config token '{token}'")
            if prune not in {"none", "monotone"}:
                raise ValueError(f"invalid prune mode in config token '{token}'")
            config_id = f"{symmetry}_{prune}"
        else:
            raise ValueError(
                f"invalid config token '{token}'; use preset ids ({', '.join(CONFIG_PRESETS.keys())}) "
                "or symmetry:prune"
            )

        if config_id in seen:
            continue
        seen.add(config_id)
        configs.append(EvalConfig(config_id=config_id, symmetry=symmetry, prune=prune))
    return configs


def _run_command(cmd: list[str], *, log_path: Path, cwd: Path) -> CommandResult:
    t0 = time.perf_counter()
    proc = subprocess.run(cmd, cwd=str(cwd), capture_output=True, text=True, check=False)
    duration = time.perf_counter() - t0
    lines = [
        "command: " + " ".join(shlex.quote(x) for x in cmd),
        f"return_code: {proc.returncode}",
        f"wall_time_sec: {duration:.6f}",
        "----- STDOUT -----",
        proc.stdout.rstrip("\n"),
        "----- STDERR -----",
        proc.stderr.rstrip("\n"),
    ]
    log_path.write_text("\n".join(lines).rstrip() + "\n", encoding="utf-8")
    if proc.returncode != 0:
        raise RuntimeError(f"command failed (rc={proc.returncode}): {' '.join(shlex.quote(x) for x in cmd)}")
    return CommandResult(returncode=proc.returncode, wall_time_sec=duration)


def _select_sample_sat_case_ids(cases: list[dict[str, Any]], *, max_samples: int) -> list[str]:
    sat_ids = {
        str(case.get("case_id", ""))
        for case in cases
        if str(case.get("status", "UNKNOWN")) == "SAT" and bool(case.get("solved", False))
    }
    selected: list[str] = []
    for cid in TRIVIALITY_SAMPLE_CASE_IDS:
        if cid in sat_ids:
            selected.append(cid)
        if len(selected) >= max_samples:
            return selected

    for cid in sorted(sat_ids):
        if cid in selected:
            continue
        selected.append(cid)
        if len(selected) >= max_samples:
            break
    return selected


def _compute_triviality(case_dir: Path) -> dict[str, float | int | bool]:
    manifest = _load_json(case_dir / "sen24.manifest.json")
    model = _load_json(case_dir / "model.json")

    nprofiles = int(manifest["nprofiles"])
    npairs = int(manifest["npairs"])
    nranks = int(manifest["nranks"])
    pair_order = [tuple(x) for x in manifest["pair_order"]]

    rankings = list(itertools.permutations([0, 1, 2, 3], 4))
    if len(rankings) != nranks:
        raise ValueError(f"ranking count mismatch: expected {nranks}, got {len(rankings)}")
    pos_maps = [{a: i for i, a in enumerate(r)} for r in rankings]

    p_true_set = {
        int(v)
        for v in model.get("true_vars", [])
        if 1 <= int(v) <= int(manifest["n_p_vars"])
    }

    total_atoms = nprofiles * npairs
    match_counts = [0, 0]
    pair_support = [0 for _ in range(npairs)]
    signatures: set[tuple[int, ...]] = set()

    for p in range(nprofiles):
        r0_idx = p // nranks
        r1_idx = p % nranks
        pos0 = pos_maps[r0_idx]
        pos1 = pos_maps[r1_idx]
        sig_bits: list[int] = []

        for pair_idx, (a, b) in enumerate(pair_order):
            var = 1 + p * npairs + pair_idx
            social = var in p_true_set
            if social:
                pair_support[pair_idx] += 1

            pref0 = pos0[a] < pos0[b]
            pref1 = pos1[a] < pos1[b]
            if social == pref0:
                match_counts[0] += 1
            if social == pref1:
                match_counts[1] += 1
            sig_bits.append(1 if social else 0)

        signatures.add(tuple(sig_bits))

    dictatorship_score_voter0 = match_counts[0] / total_atoms if total_atoms > 0 else 0.0
    dictatorship_score_voter1 = match_counts[1] / total_atoms if total_atoms > 0 else 0.0

    mode_support = max(pair_support) if pair_support else 0
    neutrality_violation_count = sum(1 for count in pair_support if count != mode_support)
    pair_constancy_score = (
        sum(max(count / nprofiles, 1.0 - (count / nprofiles)) for count in pair_support) / npairs if npairs > 0 else 0.0
    )

    distinct_social_outcomes = len(signatures)

    return {
        "dictatorship_score_voter0": float(dictatorship_score_voter0),
        "dictatorship_score_voter1": float(dictatorship_score_voter1),
        "neutrality_violation_count": int(neutrality_violation_count),
        "pair_constancy_score": float(pair_constancy_score),
        "distinct_social_outcomes": int(distinct_social_outcomes),
        "constant_function": bool(distinct_social_outcomes == 1),
    }


def _extract_run_metrics(
    *,
    atlas: dict[str, Any],
    run_dir: Path,
    wall_time_sec: float,
    config: EvalConfig,
    rep_index: int,
    triviality_sample_n: int,
    phase_times: dict[str, float],
) -> dict[str, Any]:
    cases = list(atlas.get("cases", []))
    status_counts = dict(atlas.get("status_counts", {}))

    sat_count = int(status_counts.get("SAT", 0))
    unsat_count = int(status_counts.get("UNSAT", 0))

    solved_true_count = sum(1 for c in cases if bool(c.get("solved", False)))
    solved_false_count = sum(1 for c in cases if not bool(c.get("solved", False)))

    pruned_by_reason_counts: dict[str, int] = {}
    for case in cases:
        if bool(case.get("solved", False)):
            continue
        pruned_by = case.get("pruned_by")
        if not isinstance(pruned_by, dict):
            continue
        reason = str(pruned_by.get("rule", "unknown"))
        pruned_by_reason_counts[reason] = pruned_by_reason_counts.get(reason, 0) + 1

    orbit_sizes = [int(case.get("orbit_size", 1)) for case in cases]
    orbit_stats = {
        "min": min(orbit_sizes) if orbit_sizes else 0,
        "max": max(orbit_sizes) if orbit_sizes else 0,
        "mean": _mean([float(v) for v in orbit_sizes]),
    }

    proof_cases = [
        case
        for case in cases
        if str(case.get("status", "UNKNOWN")) == "UNSAT" and isinstance(case.get("proof"), dict)
    ]
    proof_sha_count = sum(1 for case in proof_cases if str(case.get("proof", {}).get("sha256", "")) != "")
    unsat_proof_count = len(proof_cases)

    mus_sizes: list[float] = []
    for case in cases:
        mus = case.get("mus")
        if isinstance(mus, dict) and mus.get("status") == "ok":
            mus_sizes.append(float(len(list(mus.get("mus_axioms", [])))))

    sampled_case_ids = _select_sample_sat_case_ids(cases, max_samples=triviality_sample_n)
    triviality_cases: list[dict[str, Any]] = []
    for case_id in sampled_case_ids:
        case_dir = run_dir / case_id
        model_path = case_dir / "model.json"
        manifest_path = case_dir / "sen24.manifest.json"
        if not model_path.exists() or not manifest_path.exists():
            continue
        try:
            metrics = _compute_triviality(case_dir)
        except Exception:
            continue
        triviality_cases.append({"case_id": case_id, **metrics})

    d0_values = [float(item["dictatorship_score_voter0"]) for item in triviality_cases]
    d1_values = [float(item["dictatorship_score_voter1"]) for item in triviality_cases]
    ds_values = [max(a, b) for (a, b) in zip(d0_values, d1_values)]
    outcomes_values = [float(item["distinct_social_outcomes"]) for item in triviality_cases]
    const_flags = [1.0 if bool(item["constant_function"]) else 0.0 for item in triviality_cases]

    triviality_summary = {
        "sample_target_n": triviality_sample_n,
        "sampled_count": len(triviality_cases),
        "sampled_case_ids": [item["case_id"] for item in triviality_cases],
        "dictatorship_score_voter0_avg": _mean(d0_values),
        "dictatorship_score_voter1_avg": _mean(d1_values),
        "dictatorship_score_max": max(ds_values) if ds_values else 0.0,
        "distinct_social_outcomes_avg": _mean(outcomes_values),
        "distinct_social_outcomes_max": max(outcomes_values) if outcomes_values else 0.0,
        "constant_function_rate": _mean(const_flags),
    }

    solver_info = dict(atlas.get("solver_info", {}))

    return {
        "config_id": config.config_id,
        "rep": rep_index,
        "symmetry": config.symmetry,
        "prune": config.prune,
        "prune_sequential_enforced": config.prune == "monotone",
        "requested_jobs": int(atlas.get("jobs", 0)),
        "effective_jobs": 1 if config.prune == "monotone" else int(atlas.get("jobs", 0)),
        "wall_time_sec": float(wall_time_sec),
        "phase_times_sec": phase_times,
        "cases_total": int(atlas.get("cases_total", 0)),
        "sat_count": sat_count,
        "unsat_count": unsat_count,
        "solved_true_count": solved_true_count,
        "solved_false_count": solved_false_count,
        "pruned_by_reason_counts": pruned_by_reason_counts,
        "equiv_classes_total": int(atlas.get("equiv_classes_total", 0)),
        "orbit_size_stats": orbit_stats,
        "solver_info": {
            "solver_version_raw": solver_info.get("solver_version_raw", "unknown"),
            "solver_version": solver_info.get("solver_version", "unknown"),
            "solver_sha256": solver_info.get("solver_sha256", "unknown"),
        },
        "proofs": {
            "unsat_proof_count": unsat_proof_count,
            "proof_sha256_present_rate": (float(proof_sha_count) / float(unsat_proof_count)) if unsat_proof_count > 0 else 0.0,
        },
        "mus": {
            "mus_count": len(mus_sizes),
            "avg_mus_size": _mean(mus_sizes),
        },
        "triviality": triviality_summary,
    }


def _write_eval_csv(path: Path, rows: list[dict[str, Any]]) -> None:
    fieldnames = [
        "config_id",
        "rep",
        "run_seed",
        "symmetry",
        "prune",
        "prune_sequential_enforced",
        "requested_jobs",
        "effective_jobs",
        "wall_time_sec",
        "cases_total",
        "sat_count",
        "unsat_count",
        "solved_true_count",
        "solved_false_count",
        "equiv_classes_total",
        "orbit_size_min",
        "orbit_size_mean",
        "orbit_size_max",
        "solver_version",
        "unsat_proof_count",
        "proof_sha256_present_rate",
        "mus_count",
        "avg_mus_size",
        "triviality_sampled_count",
        "dictatorship_score_max",
        "distinct_social_outcomes_avg",
        "constant_function_rate",
    ]
    with path.open("w", newline="", encoding="utf-8") as f:
        writer = csv.DictWriter(f, fieldnames=fieldnames)
        writer.writeheader()
        for row in rows:
            orbit_stats = row.get("orbit_size_stats", {})
            writer.writerow(
                {
                    "config_id": row.get("config_id"),
                    "rep": row.get("rep"),
                    "run_seed": row.get("run_seed", 0),
                    "symmetry": row.get("symmetry"),
                    "prune": row.get("prune"),
                    "prune_sequential_enforced": row.get("prune_sequential_enforced", False),
                    "requested_jobs": row.get("requested_jobs", 0),
                    "effective_jobs": row.get("effective_jobs", 0),
                    "wall_time_sec": f"{float(row.get('wall_time_sec', 0.0)):.6f}",
                    "cases_total": row.get("cases_total", 0),
                    "sat_count": row.get("sat_count", 0),
                    "unsat_count": row.get("unsat_count", 0),
                    "solved_true_count": row.get("solved_true_count", 0),
                    "solved_false_count": row.get("solved_false_count", 0),
                    "equiv_classes_total": row.get("equiv_classes_total", 0),
                    "orbit_size_min": orbit_stats.get("min", 0),
                    "orbit_size_mean": f"{float(orbit_stats.get('mean', 0.0)):.6f}",
                    "orbit_size_max": orbit_stats.get("max", 0),
                    "solver_version": row.get("solver_info", {}).get("solver_version", "unknown"),
                    "unsat_proof_count": row.get("proofs", {}).get("unsat_proof_count", 0),
                    "proof_sha256_present_rate": f"{float(row.get('proofs', {}).get('proof_sha256_present_rate', 0.0)):.6f}",
                    "mus_count": row.get("mus", {}).get("mus_count", 0),
                    "avg_mus_size": f"{float(row.get('mus', {}).get('avg_mus_size', 0.0)):.6f}",
                    "triviality_sampled_count": row.get("triviality", {}).get("sampled_count", 0),
                    "dictatorship_score_max": f"{float(row.get('triviality', {}).get('dictatorship_score_max', 0.0)):.6f}",
                    "distinct_social_outcomes_avg": f"{float(row.get('triviality', {}).get('distinct_social_outcomes_avg', 0.0)):.6f}",
                    "constant_function_rate": f"{float(row.get('triviality', {}).get('constant_function_rate', 0.0)):.6f}",
                }
            )


def _aggregate_by_config(rows: list[dict[str, Any]]) -> dict[str, dict[str, Any]]:
    grouped: dict[str, list[dict[str, Any]]] = {}
    for row in rows:
        grouped.setdefault(str(row["config_id"]), []).append(row)

    summary: dict[str, dict[str, Any]] = {}
    for config_id in sorted(grouped.keys()):
        items = grouped[config_id]
        wall = [float(item["wall_time_sec"]) for item in items]
        solved_true = [float(item["solved_true_count"]) for item in items]
        solved_false = [float(item["solved_false_count"]) for item in items]
        eq_classes = [float(item["equiv_classes_total"]) for item in items]
        orbit_mean = [float(item["orbit_size_stats"]["mean"]) for item in items]
        summary[config_id] = {
            "runs": len(items),
            "wall_time_sec_mean": _mean(wall),
            "wall_time_sec_std": _stddev(wall),
            "solved_true_mean": _mean(solved_true),
            "solved_false_mean": _mean(solved_false),
            "equiv_classes_total_mean": _mean(eq_classes),
            "orbit_size_mean": _mean(orbit_mean),
        }
    return summary


def main() -> None:
    ap = argparse.ArgumentParser(description="Evaluation harness for sen24 atlas runs.")
    ap.add_argument("--outdir", type=Path, required=True, help="Root directory for evaluation outputs.")
    ap.add_argument("--solver", type=str, default="cadical", help="SAT solver path or executable name.")
    ap.add_argument("--jobs", type=int, default=1, help="Parallel jobs passed to run_atlas where safe.")
    ap.add_argument(
        "--configs",
        type=str,
        default=None,
        help=(
            "CSV config ids. Presets: none_none,alts_none,none_monotone,alts_monotone. "
            "Alternative syntax: symmetry:prune"
        ),
    )
    ap.add_argument("--repeat", type=int, default=3, help="Repetitions per config.")
    ap.add_argument("--seed", type=int, default=20260213, help="Recorded deterministic seed.")
    ap.add_argument("--dry-run", action="store_true", help="Pass --dry-run into run_atlas.")
    ap.add_argument(
        "--case-masks",
        type=str,
        default=None,
        help="Optional mask subset forwarded to run_atlas (useful for smoke/eval sanity runs).",
    )
    ap.add_argument(
        "--triviality-sample-n",
        type=int,
        default=5,
        help="How many SAT cases to sample for triviality metrics.",
    )
    args = ap.parse_args()

    if args.repeat < 1:
        raise ValueError("--repeat must be >= 1")
    if args.jobs < 1:
        raise ValueError("--jobs must be >= 1")
    if args.triviality_sample_n < 1:
        raise ValueError("--triviality-sample-n must be >= 1")

    configs = _parse_configs(args.configs)
    outdir = args.outdir
    runs_root = outdir / "runs"
    outdir.mkdir(parents=True, exist_ok=True)
    runs_root.mkdir(parents=True, exist_ok=True)

    solver_path_raw = _resolve_solver_path(args.solver)
    solver_sha256 = "unknown"
    if solver_path_raw is not None:
        try:
            solver_sha256 = _sha256_file(Path(solver_path_raw))
        except OSError:
            solver_sha256 = "unknown"
    solver_path = _sanitize_solver_path(solver_path_raw)

    run_rows: list[dict[str, Any]] = []
    run_records: list[dict[str, Any]] = []
    run_seeds: list[int] = []
    run_index = 0

    for config in configs:
        for rep in range(1, args.repeat + 1):
            run_seed = int(args.seed + run_index)
            run_index += 1
            run_seeds.append(run_seed)
            run_dir = runs_root / config.config_id / f"rep_{rep:02d}"
            run_dir.mkdir(parents=True, exist_ok=True)

            start = time.perf_counter()
            phase_times: dict[str, float] = {}

            run_atlas_cmd = [
                sys.executable,
                str(RUN_ATLAS),
                "--outdir",
                str(run_dir),
                "--solver",
                args.solver,
                "--jobs",
                str(args.jobs),
                "--symmetry",
                config.symmetry,
                "--prune",
                config.prune,
                "--emit-proof",
                "unsat-only",
            ]
            if args.dry_run:
                run_atlas_cmd.append("--dry-run")
            if args.case_masks is not None:
                run_atlas_cmd.extend(["--case-masks", args.case_masks])

            result_run_atlas = _run_command(
                run_atlas_cmd,
                log_path=run_dir / "eval_run_atlas.log",
                cwd=SCRIPT_DIR.parent,
            )
            phase_times["run_atlas_sec"] = result_run_atlas.wall_time_sec

            atlas_path = run_dir / "atlas.json"
            if not atlas_path.exists():
                raise RuntimeError(f"missing atlas output: {atlas_path}")
            atlas = _load_json(atlas_path)

            unsat_solved_count = sum(
                1
                for case in atlas.get("cases", [])
                if str(case.get("status", "UNKNOWN")) == "UNSAT" and bool(case.get("solved", False))
            )

            mus_ran = False
            if (not args.dry_run) and unsat_solved_count > 0:
                mus_cmd = [
                    sys.executable,
                    str(MUS_MCS),
                    "--outdir",
                    str(run_dir),
                    "--solver",
                    args.solver,
                ]
                result_mus = _run_command(
                    mus_cmd,
                    log_path=run_dir / "eval_mus_mcs.log",
                    cwd=SCRIPT_DIR.parent,
                )
                phase_times["mus_mcs_sec"] = result_mus.wall_time_sec
                mus_ran = True
                atlas = _load_json(atlas_path)
            else:
                phase_times["mus_mcs_sec"] = 0.0

            summarize_cmd = [
                sys.executable,
                str(SUMMARIZE),
                "--outdir",
                str(run_dir),
            ]
            result_summarize = _run_command(
                summarize_cmd,
                log_path=run_dir / "eval_summarize.log",
                cwd=SCRIPT_DIR.parent,
            )
            phase_times["summarize_sec"] = result_summarize.wall_time_sec

            wall_time_sec = time.perf_counter() - start
            metrics = _extract_run_metrics(
                atlas=atlas,
                run_dir=run_dir,
                wall_time_sec=wall_time_sec,
                config=config,
                rep_index=rep,
                triviality_sample_n=args.triviality_sample_n,
                phase_times=phase_times,
            )
            metrics["mus_ran"] = mus_ran
            metrics["seed"] = args.seed
            metrics["run_seed"] = run_seed
            metrics["run_dir"] = str(run_dir)

            _write_json(run_dir / "run_metrics.json", metrics)
            run_rows.append(metrics)
            run_records.append(
                {
                    "config_id": config.config_id,
                    "rep": rep,
                    "run_seed": run_seed,
                    "run_dir": str(run_dir),
                    "run_metrics": metrics,
                }
            )

    solver_version_raw = "unknown"
    solver_version = "unknown"
    if run_rows:
        solver_info0 = dict(run_rows[0].get("solver_info", {}))
        solver_version_raw = str(solver_info0.get("solver_version_raw", "unknown"))
        solver_version = str(solver_info0.get("solver_version", "unknown"))

    eval_obj: dict[str, Any] = {
        "eval_schema_version": EVAL_SCHEMA_VERSION,
        "generated_at_utc": datetime.now(timezone.utc).isoformat(),
        "n": 2,
        "m": 4,
        "seed": args.seed,
        "seed_policy": "deterministic-sequence (run_seed = seed + run_index; record-only)",
        "seeds": run_seeds,
        "repeat": args.repeat,
        "solver": args.solver,
        "jobs": args.jobs,
        "dry_run": args.dry_run,
        "configs": [config.config_id for config in configs],
        "case_masks": args.case_masks,
        "triviality_sample_n": args.triviality_sample_n,
        "runs": run_records,
        "config_summary": _aggregate_by_config(run_rows),
        "reproducibility": {
            "git": {"commit": _probe_git_commit()},
            "python": {"version": sys.version.split()[0]},
            "platform": py_platform.platform(),
            "solver": {
                "name": args.solver,
                "path": solver_path,
                "sha256": solver_sha256,
                "version_raw": solver_version_raw,
                "version": solver_version,
            },
        },
    }

    eval_json_path = outdir / "eval.json"
    eval_csv_path = outdir / "eval.csv"
    _write_json(eval_json_path, eval_obj)
    _write_eval_csv(eval_csv_path, run_rows)

    print(f"Wrote {eval_json_path}")
    print(f"Wrote {eval_csv_path}")


if __name__ == "__main__":
    main()
