#!/usr/bin/env python3
from __future__ import annotations

import argparse
import hashlib
import itertools
import json
import shlex
import shutil
import subprocess
import sys
import time
from collections import Counter
from concurrent.futures import ThreadPoolExecutor, as_completed
from dataclasses import dataclass
from datetime import datetime, timezone
from functools import lru_cache
from pathlib import Path
from typing import Any

SCRIPT_DIR = Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

from gen_dimacs import run_generation  # noqa: E402


SUPPORTED_AXIOMS = ["asymm", "un", "minlib", "no_cycle3", "no_cycle4"]
ALT_VALUES = (0, 1, 2, 3)


@dataclass(frozen=True)
class CaseSpec:
    mask: int
    bitstring: str
    case_id: str
    axioms_on: list[str]
    axioms_off: list[str]


def _sha256_file(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as f:
        for chunk in iter(lambda: f.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def _popcount(mask: int) -> int:
    return bin(mask).count("1")


def parse_axiom_list(raw: str) -> list[str]:
    names = [name.strip() for name in raw.split(",") if name.strip()]
    if not names:
        raise ValueError("Axiom universe must not be empty.")
    unknown = [name for name in names if name not in SUPPORTED_AXIOMS]
    if unknown:
        raise ValueError(f"Unknown axiom name(s): {', '.join(unknown)}")
    if len(set(names)) != len(names):
        raise ValueError("Axiom universe contains duplicates.")
    return names


def parse_case_masks(raw: str | None, total_bits: int) -> list[int] | None:
    if raw is None:
        return None
    items = [x.strip() for x in raw.split(",") if x.strip()]
    if not items:
        raise ValueError("--case-masks requires at least one integer")
    masks: list[int] = []
    max_mask = (1 << total_bits) - 1
    for item in items:
        mask = int(item)
        if mask < 0 or mask > max_mask:
            raise ValueError(f"mask {mask} is out of range [0, {max_mask}]")
        masks.append(mask)
    return sorted(set(masks))


def make_cases(axiom_universe: list[str], case_masks: list[int] | None) -> list[CaseSpec]:
    k = len(axiom_universe)
    masks = list(range(1 << k)) if case_masks is None else case_masks
    cases: list[CaseSpec] = []
    for mask in masks:
        bitstring = "".join("1" if ((mask >> i) & 1) else "0" for i in range(k))
        axioms_on = [axiom_universe[i] for i in range(k) if (mask >> i) & 1]
        axioms_off = [a for a in axiom_universe if a not in axioms_on]
        cases.append(
            CaseSpec(
                mask=mask,
                bitstring=bitstring,
                case_id=f"case_{bitstring}",
                axioms_on=axioms_on,
                axioms_off=axioms_off,
            )
        )
    return cases


def _extract_status(text: str, return_code: int | None) -> str:
    if return_code == 10:
        return "SAT"
    if return_code == 20:
        return "UNSAT"
    upper = text.upper()
    if "UNSATISFIABLE" in upper:
        return "UNSAT"
    if "SATISFIABLE" in upper:
        return "SAT"
    if " UNKNOWN" in f" {upper} ":
        return "UNKNOWN"
    return "UNKNOWN"


def _parse_true_vars_from_v_lines(text: str, nvars: int) -> list[int]:
    true_vars: set[int] = set()
    for raw_line in text.splitlines():
        line = raw_line.strip()
        if not line or not (line.startswith("v ") or line == "v" or line.startswith("V ")):
            continue
        payload = line[1:].strip()
        for tok in payload.split():
            try:
                lit = int(tok)
            except ValueError:
                continue
            if 0 < lit <= nvars:
                true_vars.add(lit)
    return sorted(true_vars)


def _has_v_lines(text: str) -> bool:
    for raw_line in text.splitlines():
        line = raw_line.strip()
        if line == "v" or line.startswith("v ") or line.startswith("V "):
            return True
    return False


def _parse_true_vars_from_model_file(text: str, nvars: int) -> list[int]:
    true_vars: set[int] = set()
    for raw_line in text.splitlines():
        line = raw_line.strip()
        if not line or line.startswith("c") or line.startswith("s"):
            continue
        payload = line
        if line.startswith("v ") or line == "v" or line.startswith("V "):
            payload = line[1:].strip()
        for tok in payload.split():
            try:
                lit = int(tok)
            except ValueError:
                continue
            if 0 < lit <= nvars:
                true_vars.add(lit)
    return sorted(true_vars)


def _build_solver_cmd(
    *,
    solver: str,
    solver_template: str | None,
    cnf_path: Path,
    proof_path: Path,
    model_path: Path,
    with_proof: bool,
) -> list[str]:
    if solver_template is not None:
        rendered = solver_template.format(
            solver=solver,
            cnf=str(cnf_path),
            proof=str(proof_path),
            model=str(model_path),
        )
        return shlex.split(rendered)

    if solver == "cadical":
        if with_proof:
            return [
                solver,
                "-w",
                str(model_path),
                "--lrat",
                "--no-binary",
                str(cnf_path),
                str(proof_path),
            ]
        return [solver, "-w", str(model_path), str(cnf_path)]
    return [solver, str(cnf_path)]


def _write_solver_log(
    path: Path,
    *,
    dry_run: bool,
    attempts: list[dict[str, object]],
) -> None:
    lines: list[str] = []
    lines.append(f"dry_run: {dry_run}")
    for idx, attempt in enumerate(attempts, start=1):
        lines.append(f"attempt: {idx}")
        lines.append(f"with_proof: {attempt.get('with_proof')}")
        cmd = attempt.get("cmd")
        if cmd is not None:
            lines.append("command: " + " ".join(shlex.quote(str(x)) for x in cmd))
        lines.append(f"return_code: {attempt.get('return_code')}")
        duration_sec = float(attempt.get("duration_sec", 0.0))
        lines.append(f"duration_sec: {duration_sec:.6f}")
        error = attempt.get("error")
        if error is not None:
            lines.append(f"error: {error}")
        lines.append("----- STDOUT -----")
        lines.append(str(attempt.get("stdout", "")).rstrip("\n"))
        lines.append("----- STDERR -----")
        lines.append(str(attempt.get("stderr", "")).rstrip("\n"))
        lines.append("")
    path.write_text("\n".join(lines).rstrip() + "\n", encoding="utf-8")


def run_case(
    case: CaseSpec,
    *,
    outdir: Path,
    solver: str,
    solver_template: str | None,
    dry_run: bool,
    emit_proof_mode: str,
) -> dict[str, object]:
    case_dir = outdir / case.case_id
    case_dir.mkdir(parents=True, exist_ok=True)

    cnf_path = case_dir / "sen24.cnf"
    manifest_path = case_dir / "sen24.manifest.json"
    solver_log_path = case_dir / "solver.log"
    summary_path = case_dir / "summary.json"
    proof_path = case_dir / "proof.lrat"
    model_path = case_dir / "model.txt"
    model_json_path = case_dir / "model.json"
    for stale in (proof_path, model_path, model_json_path):
        if stale.exists():
            stale.unlink()

    manifest = run_generation(
        n=2,
        m=4,
        axiom_names=case.axioms_on,
        out_path=cnf_path,
        manifest_path=manifest_path,
    )

    status = "UNKNOWN"
    return_code: int | None = None
    command: list[str] | None = None
    duration_sec = 0.0
    model_true_vars: list[int] = []
    model_observed = False
    proof_file: str | None = None
    solver_error: str | None = None
    attempts: list[dict[str, object]] = []
    solved = False

    if dry_run:
        _write_solver_log(
            solver_log_path,
            dry_run=True,
            attempts=[
                {
                    "with_proof": False,
                    "cmd": None,
                    "return_code": None,
                    "duration_sec": 0.0,
                    "stdout": "dry-run: solver execution skipped",
                    "stderr": "",
                    "error": None,
                }
            ],
        )
    else:

        def execute_attempt(with_proof: bool) -> tuple[str, dict[str, object]]:
            cmd = _build_solver_cmd(
                solver=solver,
                solver_template=solver_template,
                cnf_path=cnf_path,
                proof_path=proof_path,
                model_path=model_path,
                with_proof=with_proof,
            )
            t0 = time.perf_counter()
            try:
                proc = subprocess.run(cmd, capture_output=True, text=True, check=False)
                took = time.perf_counter() - t0
                status_local = _extract_status(f"{proc.stdout}\n{proc.stderr}", proc.returncode)
                return (
                    status_local,
                    {
                        "with_proof": with_proof,
                        "cmd": cmd,
                        "return_code": proc.returncode,
                        "duration_sec": took,
                        "stdout": proc.stdout,
                        "stderr": proc.stderr,
                        "error": None,
                    },
                )
            except FileNotFoundError as ex:
                took = time.perf_counter() - t0
                return (
                    "UNKNOWN",
                    {
                        "with_proof": with_proof,
                        "cmd": cmd,
                        "return_code": None,
                        "duration_sec": took,
                        "stdout": "",
                        "stderr": "",
                        "error": str(ex),
                    },
                )

        first_with_proof = emit_proof_mode == "always"
        status, attempt = execute_attempt(first_with_proof)
        attempts.append(attempt)

        if status == "UNSAT" and emit_proof_mode == "unsat-only":
            if not proof_path.exists():
                status2, attempt2 = execute_attempt(True)
                attempts.append(attempt2)
                if status2 != "UNKNOWN":
                    status = status2

        duration_sec = sum(float(at.get("duration_sec", 0.0)) for at in attempts)
        command = list(attempts[-1]["cmd"]) if attempts and attempts[-1].get("cmd") is not None else None
        return_code = attempts[-1].get("return_code") if attempts else None
        if attempts and attempts[-1].get("error") is not None:
            solver_error = str(attempts[-1].get("error"))
        solved = solver_error is None and command is not None

        _write_solver_log(solver_log_path, dry_run=False, attempts=attempts)

        if status == "SAT":
            stdout_all = "\n".join(str(at.get("stdout", "")) for at in attempts)
            model_observed = _has_v_lines(stdout_all)
            model_true_vars = _parse_true_vars_from_v_lines(stdout_all, int(manifest["nvars"]))
            if model_path.exists():
                model_text = model_path.read_text(encoding="utf-8", errors="ignore")
                model_observed = model_observed or _has_v_lines(model_text)
                if not model_true_vars:
                    model_true_vars = _parse_true_vars_from_model_file(model_text, int(manifest["nvars"]))
        if status == "UNSAT" and proof_path.exists():
            proof_file = proof_path.name

    model_stats: dict[str, object] | None = None
    if status == "SAT" and model_observed:
        n_p_vars = int(manifest["n_p_vars"])
        p_true_count = sum(1 for v in model_true_vars if 1 <= v <= n_p_vars)
        aux_true_count = len(model_true_vars) - p_true_count
        density = float(p_true_count) / float(n_p_vars) if n_p_vars > 0 else 0.0
        model_stats = {
            "n_true": len(model_true_vars),
            "n_p_true": p_true_count,
            "n_aux_true": aux_true_count,
            "social_true_density": density,
        }
        model_json_path.write_text(
            json.dumps(
                {
                    "nvars": int(manifest["nvars"]),
                    "n_p_vars": n_p_vars,
                    "n_true": len(model_true_vars),
                    "n_p_true": p_true_count,
                    "n_aux_true": aux_true_count,
                    "social_true_density": density,
                    "true_vars": model_true_vars,
                },
                indent=2,
                sort_keys=True,
            )
            + "\n",
            encoding="utf-8",
        )

    proof: dict[str, object] | None = None
    if status == "UNSAT" and proof_file is not None:
        proof_sha256 = _sha256_file(proof_path)
        proof_cmd = None
        for at in reversed(attempts):
            if bool(at.get("with_proof")) and at.get("cmd") is not None:
                proof_cmd = " ".join(shlex.quote(str(x)) for x in list(at["cmd"]))
                break
        proof = {
            "format": "lrat",
            "path": proof_file,
            "sha256": proof_sha256,
            "solver": solver,
            "cmd": proof_cmd,
        }

    summary: dict[str, object] = {
        "case_id": case.case_id,
        "mask_int": case.mask,
        "mask_bits": case.bitstring,
        "axioms_on": case.axioms_on,
        "axioms_off": case.axioms_off,
        "status": status,
        "solved": solved,
        "inferred": False,
        "dry_run": dry_run,
        "solver": solver,
        "solver_template": solver_template,
        "command": command,
        "return_code": return_code,
        "duration_sec": duration_sec,
        "solver_error": solver_error,
        "proof_file": proof_file,
        "proof": proof,
        "model_file": model_json_path.name if model_json_path.exists() else None,
        "model_stats": model_stats,
        "files": {
            "cnf": cnf_path.name,
            "manifest": manifest_path.name,
            "solver_log": solver_log_path.name,
            "summary": summary_path.name,
        },
        "reproduce": {
            "command": (
                f"python3 scripts/run_atlas.py --outdir <atlas_outdir> --case-masks {case.mask} "
                f"--jobs 1 --prune none --emit-proof {emit_proof_mode}"
            ),
            "case_mask": case.mask,
            "case_bits": case.bitstring,
            "axioms_on": case.axioms_on,
        },
        "manifest": {
            "nvars": int(manifest["nvars"]),
            "nclauses": int(manifest["nclauses"]),
            "cnf_sha256": manifest.get("cnf_sha256"),
            "category_counts": manifest["category_counts"],
            "minlib": manifest["minlib"],
        },
    }
    summary_path.write_text(json.dumps(summary, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return summary


def _make_pruned_summary(
    case: CaseSpec,
    *,
    status: str,
    witness_mask: int,
    witness_case_id: str,
    rule: str,
    dry_run: bool,
    solver: str,
    solver_template: str | None,
    emit_proof_mode: str,
) -> dict[str, object]:
    return {
        "case_id": case.case_id,
        "mask_int": case.mask,
        "mask_bits": case.bitstring,
        "axioms_on": case.axioms_on,
        "axioms_off": case.axioms_off,
        "status": status,
        "solved": False,
        "inferred": True,
        "pruned_by": {
            "rule": rule,
            "witness_case": witness_case_id,
            "witness_mask": witness_mask,
            "witness_bits": format(witness_mask, f"0{len(case.bitstring)}b"),
            "witness_status": status,
        },
        "dry_run": dry_run,
        "solver": solver,
        "solver_template": solver_template,
        "command": None,
        "return_code": None,
        "duration_sec": 0.0,
        "solver_error": None,
        "proof_file": None,
        "proof": None,
        "model_file": None,
        "model_stats": None,
        "files": {
            "cnf": None,
            "manifest": None,
            "solver_log": None,
            "summary": None,
        },
        "reproduce": {
            "command": (
                f"python3 scripts/run_atlas.py --outdir <atlas_outdir> --case-masks {case.mask} "
                f"--jobs 1 --prune none --emit-proof {emit_proof_mode}"
            ),
            "case_mask": case.mask,
            "case_bits": case.bitstring,
            "axioms_on": case.axioms_on,
            "inferred_by": {
                "rule": rule,
                "witness_case": witness_case_id,
                "witness_mask": witness_mask,
            },
        },
        "manifest": None,
    }


def _pick_sat_superset(mask: int, known_sat: dict[int, str]) -> tuple[int, str] | None:
    candidates = [m for m in known_sat.keys() if (mask & m) == mask]
    if not candidates:
        return None
    witness = sorted(candidates, key=lambda m: (_popcount(m), m))[0]
    return witness, known_sat[witness]


def _pick_unsat_subset(mask: int, known_unsat: dict[int, str]) -> tuple[int, str] | None:
    candidates = [m for m in known_unsat.keys() if (m & mask) == m]
    if not candidates:
        return None
    witness = sorted(candidates, key=lambda m: (-_popcount(m), m))[0]
    return witness, known_unsat[witness]


def _verify_pruned_cases(
    *,
    cases: list[CaseSpec],
    summaries_by_mask: dict[int, dict[str, object]],
    outdir: Path,
    solver: str,
    solver_template: str | None,
    emit_proof_mode: str,
) -> dict[str, object]:
    pruned_cases = []
    for case in sorted(cases, key=lambda c: c.mask):
        summary = summaries_by_mask[case.mask]
        if bool(summary.get("solved")):
            continue
        if summary.get("pruned_by") is None:
            continue
        status = str(summary.get("status", "UNKNOWN"))
        if status not in {"SAT", "UNSAT"}:
            continue
        pruned_cases.append(case)

    sample = pruned_cases[:3]
    if not sample:
        return {"enabled": True, "checked": 0, "mismatches": 0, "sample_case_ids": []}

    check_dir = outdir / "_prune_check"
    if check_dir.exists():
        shutil.rmtree(check_dir)
    mismatches: list[dict[str, object]] = []
    for case in sample:
        expected = str(summaries_by_mask[case.mask].get("status", "UNKNOWN"))
        direct = run_case(
            case,
            outdir=check_dir,
            solver=solver,
            solver_template=solver_template,
            dry_run=False,
            emit_proof_mode=emit_proof_mode,
        )
        observed = str(direct.get("status", "UNKNOWN"))
        if observed != expected:
            mismatches.append(
                {
                    "case_id": case.case_id,
                    "expected": expected,
                    "observed": observed,
                }
            )
    shutil.rmtree(check_dir, ignore_errors=True)
    if mismatches:
        raise RuntimeError(f"monotone prune check failed: {mismatches}")
    return {
        "enabled": True,
        "checked": len(sample),
        "mismatches": 0,
        "sample_case_ids": [c.case_id for c in sample],
    }


def run_all_cases(
    cases: list[CaseSpec],
    *,
    outdir: Path,
    solver: str,
    solver_template: str | None,
    dry_run: bool,
    emit_proof_mode: str,
    jobs: int,
    prune: str,
    prune_check: bool,
) -> tuple[list[dict[str, object]], dict[str, object], dict[str, object]]:
    if prune == "none":
        if jobs <= 1:
            summaries = [
                run_case(
                    case,
                    outdir=outdir,
                    solver=solver,
                    solver_template=solver_template,
                    dry_run=dry_run,
                    emit_proof_mode=emit_proof_mode,
                )
                for case in cases
            ]
        else:
            results_by_id: dict[str, dict[str, object]] = {}
            with ThreadPoolExecutor(max_workers=jobs) as pool:
                futures = {
                    pool.submit(
                        run_case,
                        case,
                        outdir=outdir,
                        solver=solver,
                        solver_template=solver_template,
                        dry_run=dry_run,
                        emit_proof_mode=emit_proof_mode,
                    ): case
                    for case in cases
                }
                for fut in as_completed(futures):
                    summary = fut.result()
                    results_by_id[str(summary["case_id"])] = summary
            summaries = [results_by_id[case.case_id] for case in cases]

        solver_calls = sum(1 for s in summaries if bool(s.get("solved", False)))
        prune_stats = {
            "mode": "none",
            "solver_calls": solver_calls,
            "solver_calls_avoided": 0,
            "pruned_total": 0,
            "pruned_sat": 0,
            "pruned_unsat": 0,
            "prune_check": {"enabled": False, "checked": 0, "mismatches": 0, "sample_case_ids": []},
        }
        oracle_stats = {
            "known_sat": sum(1 for s in summaries if s.get("status") == "SAT"),
            "known_unsat": sum(1 for s in summaries if s.get("status") == "UNSAT"),
            "sat_inferred": 0,
            "unsat_inferred": 0,
            "conflict_hits": 0,
        }
        return summaries, prune_stats, oracle_stats

    if prune != "monotone":
        raise ValueError(f"Unsupported prune mode: {prune}")

    ordered_cases = sorted(cases, key=lambda c: (-_popcount(c.mask), c.mask))
    results_by_mask: dict[int, dict[str, object]] = {}
    known_sat: dict[int, str] = {}
    known_unsat: dict[int, str] = {}
    solver_calls = 0
    pruned_sat = 0
    pruned_unsat = 0
    conflict_hits = 0

    for case in ordered_cases:
        sat_witness = _pick_sat_superset(case.mask, known_sat)
        unsat_witness = _pick_unsat_subset(case.mask, known_unsat)
        if sat_witness is not None and unsat_witness is not None:
            conflict_hits += 1
            raise RuntimeError(
                f"Monotone pruning conflict for {case.case_id}: "
                f"SAT witness {sat_witness[1]} and UNSAT witness {unsat_witness[1]}"
            )
        if sat_witness is not None:
            witness_mask, witness_case_id = sat_witness
            summary = _make_pruned_summary(
                case,
                status="SAT",
                witness_mask=witness_mask,
                witness_case_id=witness_case_id,
                rule="sat_superset",
                dry_run=dry_run,
                solver=solver,
                solver_template=solver_template,
                emit_proof_mode=emit_proof_mode,
            )
            results_by_mask[case.mask] = summary
            known_sat[case.mask] = case.case_id
            pruned_sat += 1
            continue

        if unsat_witness is not None:
            witness_mask, witness_case_id = unsat_witness
            summary = _make_pruned_summary(
                case,
                status="UNSAT",
                witness_mask=witness_mask,
                witness_case_id=witness_case_id,
                rule="unsat_subset",
                dry_run=dry_run,
                solver=solver,
                solver_template=solver_template,
                emit_proof_mode=emit_proof_mode,
            )
            results_by_mask[case.mask] = summary
            known_unsat[case.mask] = case.case_id
            pruned_unsat += 1
            continue

        summary = run_case(
            case,
            outdir=outdir,
            solver=solver,
            solver_template=solver_template,
            dry_run=dry_run,
            emit_proof_mode=emit_proof_mode,
        )
        results_by_mask[case.mask] = summary
        if bool(summary.get("solved")):
            solver_calls += 1
        status = str(summary.get("status", "UNKNOWN"))
        if status == "SAT":
            known_sat[case.mask] = case.case_id
        elif status == "UNSAT":
            known_unsat[case.mask] = case.case_id

    prune_check_summary = {"enabled": False, "checked": 0, "mismatches": 0, "sample_case_ids": []}
    if prune_check and not dry_run:
        prune_check_summary = _verify_pruned_cases(
            cases=cases,
            summaries_by_mask=results_by_mask,
            outdir=outdir,
            solver=solver,
            solver_template=solver_template,
            emit_proof_mode=emit_proof_mode,
        )

    summaries = [results_by_mask[case.mask] for case in cases]
    prune_total = pruned_sat + pruned_unsat
    prune_stats = {
        "mode": "monotone",
        "solver_calls": solver_calls,
        "solver_calls_avoided": prune_total,
        "pruned_total": prune_total,
        "pruned_sat": pruned_sat,
        "pruned_unsat": pruned_unsat,
        "prune_check": prune_check_summary,
    }
    oracle_stats = {
        "known_sat": len(known_sat),
        "known_unsat": len(known_unsat),
        "sat_inferred": pruned_sat,
        "unsat_inferred": pruned_unsat,
        "conflict_hits": conflict_hits,
    }
    return summaries, prune_stats, oracle_stats


def _stable_hash_payload(prefix: str, payload: dict[str, object]) -> str:
    raw = json.dumps(payload, sort_keys=True, separators=(",", ":"))
    digest = hashlib.sha256(raw.encode("utf-8")).hexdigest()
    return f"{prefix}:{digest}"


@lru_cache(maxsize=8)
def _alt_permutation_maps(
    pair_order_key: tuple[tuple[int, int], ...],
    nranks: int,
) -> tuple[tuple[tuple[int, ...], ...], tuple[tuple[int, ...], ...]]:
    pair_to_idx = {pair: idx for idx, pair in enumerate(pair_order_key)}
    rankings = list(itertools.permutations(ALT_VALUES, len(ALT_VALUES)))
    if len(rankings) != nranks:
        raise ValueError(f"Expected nranks={nranks}, got {len(rankings)} from permutation enumeration.")
    ranking_to_idx = {ranking: idx for idx, ranking in enumerate(rankings)}

    profile_maps: list[tuple[int, ...]] = []
    pair_maps: list[tuple[int, ...]] = []
    for perm in itertools.permutations(ALT_VALUES, len(ALT_VALUES)):
        inv = [0] * len(ALT_VALUES)
        for src, dst in enumerate(perm):
            inv[dst] = src

        pair_map = tuple(pair_to_idx[(inv[a], inv[b])] for (a, b) in pair_order_key)
        pair_maps.append(pair_map)

        profile_map: list[int] = []
        for r0_idx in range(nranks):
            r0_target = rankings[r0_idx]
            r0_orig = tuple(inv[x] for x in r0_target)
            r0_orig_idx = ranking_to_idx[r0_orig]
            for r1_idx in range(nranks):
                r1_target = rankings[r1_idx]
                r1_orig = tuple(inv[x] for x in r1_target)
                r1_orig_idx = ranking_to_idx[r1_orig]
                profile_map.append(r0_orig_idx * nranks + r1_orig_idx)
        profile_maps.append(tuple(profile_map))

    return tuple(profile_maps), tuple(pair_maps)


def _canonical_sat_signature_alts(
    *,
    true_vars: list[int],
    nprofiles: int,
    npairs: int,
    nranks: int,
    pair_order: list[tuple[int, int]],
) -> tuple[str, float]:
    n_p_vars = nprofiles * npairs
    social_bits = bytearray(n_p_vars)
    for var in true_vars:
        if 1 <= var <= n_p_vars:
            social_bits[var - 1] = 1

    pair_key = tuple(pair_order)
    profile_maps, pair_maps = _alt_permutation_maps(pair_key, nranks)
    best: bytes | None = None
    for profile_map, pair_map in zip(profile_maps, pair_maps):
        transformed = bytearray(n_p_vars)
        dst = 0
        for p_tgt in range(nprofiles):
            p_src = profile_map[p_tgt]
            base_src = p_src * npairs
            for pair_tgt in range(npairs):
                transformed[dst] = social_bits[base_src + pair_map[pair_tgt]]
                dst += 1
        as_bytes = bytes(transformed)
        if best is None or as_bytes < best:
            best = as_bytes
    if best is None:
        best = bytes(n_p_vars)
    density = float(sum(best)) / float(len(best)) if best else 0.0
    digest = hashlib.sha256(best).hexdigest()
    return f"sat_alts:{digest}", density


def _case_semantic_signature(
    summary: dict[str, object],
    *,
    outdir: Path,
    symmetry_mode: str,
) -> tuple[str, dict[str, object]]:
    case_id = str(summary.get("case_id", ""))
    status = str(summary.get("status", "UNKNOWN"))
    solved = bool(summary.get("solved", False))
    metrics: dict[str, object] = {}

    if symmetry_mode == "alts" and status == "SAT" and solved:
        model_file = summary.get("model_file")
        if isinstance(model_file, str) and model_file:
            case_dir = outdir / case_id
            model_path = case_dir / model_file
            manifest_path = case_dir / "sen24.manifest.json"
            if model_path.exists() and manifest_path.exists():
                model_obj = json.loads(model_path.read_text(encoding="utf-8"))
                manifest_obj = json.loads(manifest_path.read_text(encoding="utf-8"))
                npairs = int(manifest_obj["npairs"])
                nprofiles = int(manifest_obj["nprofiles"])
                nranks = int(manifest_obj["nranks"])
                pair_order = [tuple(x) for x in manifest_obj["pair_order"]]
                true_vars = [int(v) for v in model_obj.get("true_vars", [])]
                sig, density = _canonical_sat_signature_alts(
                    true_vars=true_vars,
                    nprofiles=nprofiles,
                    npairs=npairs,
                    nranks=nranks,
                    pair_order=pair_order,
                )
                metrics["social_true_density"] = density
                return sig, metrics

    if status == "UNSAT":
        payload: dict[str, object] = {
            "status": status,
            "axioms_on": list(summary.get("axioms_on", [])),
            "solved": solved,
        }
        proof = summary.get("proof")
        if isinstance(proof, dict):
            payload["proof_sha256"] = proof.get("sha256")
        mus = summary.get("mus")
        if isinstance(mus, dict):
            payload["mus_bits"] = mus.get("mus_bits")
        return _stable_hash_payload("unsat", payload), metrics

    if not solved:
        payload = {
            "status": status,
            "axioms_on": list(summary.get("axioms_on", [])),
            "pruned_by": summary.get("pruned_by"),
        }
        return _stable_hash_payload("inferred", payload), metrics

    payload = {
        "status": status,
        "axioms_on": list(summary.get("axioms_on", [])),
        "mask_bits": summary.get("mask_bits"),
    }
    return _stable_hash_payload("fallback", payload), metrics


def apply_symmetry_classes(
    summaries: list[dict[str, object]],
    *,
    outdir: Path,
    symmetry_mode: str,
) -> tuple[list[dict[str, object]], dict[str, object]]:
    sig_by_case: dict[str, str] = {}
    metrics_by_case: dict[str, dict[str, object]] = {}
    for summary in summaries:
        case_id = str(summary.get("case_id"))
        signature, metrics = _case_semantic_signature(summary, outdir=outdir, symmetry_mode=symmetry_mode)
        sig_by_case[case_id] = signature
        metrics_by_case[case_id] = metrics

    class_members: dict[str, list[str]] = {}
    class_payload: dict[str, str] = {}
    for case_id, signature in sig_by_case.items():
        class_id = "eq_" + hashlib.sha256(signature.encode("utf-8")).hexdigest()[:16]
        class_members.setdefault(class_id, []).append(case_id)
        class_payload[class_id] = signature

    case_index = {str(s["case_id"]): s for s in summaries}
    class_summaries: dict[str, dict[str, object]] = {}
    for class_id in sorted(class_members.keys()):
        members = sorted(class_members[class_id])
        representative = members[0]
        statuses = Counter(str(case_index[cid].get("status", "UNKNOWN")) for cid in members)
        sat_density_vals = [
            float(metrics_by_case[cid]["social_true_density"])
            for cid in members
            if "social_true_density" in metrics_by_case[cid]
        ]
        class_summary: dict[str, object] = {
            "class_id": class_id,
            "representative_case": representative,
            "orbit_size": len(members),
            "cases": members,
            "status_counts": dict(statuses),
            "signature_hash": hashlib.sha256(class_payload[class_id].encode("utf-8")).hexdigest(),
        }
        if sat_density_vals:
            class_summary["triviality"] = {
                "social_true_density_min": min(sat_density_vals),
                "social_true_density_max": max(sat_density_vals),
            }
        class_summaries[class_id] = class_summary

    for summary in summaries:
        case_id = str(summary["case_id"])
        signature = sig_by_case[case_id]
        class_id = "eq_" + hashlib.sha256(signature.encode("utf-8")).hexdigest()[:16]
        members = sorted(class_members[class_id])
        summary["equiv_class_id"] = class_id
        summary["representative_case"] = members[0]
        summary["orbit_size"] = len(members)

    class_hist = Counter(len(v) for v in class_members.values())
    representatives = sorted({sorted(v)[0] for v in class_members.values()})
    unsat_classes = sum(
        1 for class_id in class_summaries if int(class_summaries[class_id]["status_counts"].get("UNSAT", 0)) > 0
    )
    top_level = {
        "symmetry_mode": symmetry_mode,
        "equiv_classes_total": len(class_members),
        "equiv_class_histogram": {str(k): class_hist[k] for k in sorted(class_hist.keys())},
        "representatives": representatives,
        "unsat_equiv_classes": unsat_classes,
        "equiv_classes": class_summaries,
    }
    return summaries, top_level


def default_outdir() -> Path:
    stamp = datetime.now().strftime("%Y%m%d")
    return Path("results") / stamp / "atlas_v1"


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument(
        "--axiom-universe",
        type=str,
        default="asymm,un,minlib,no_cycle3,no_cycle4",
        help="Comma-separated axiom universe order used for stable bitmasks.",
    )
    ap.add_argument(
        "--outdir",
        type=Path,
        default=default_outdir(),
        help="Atlas output directory (default: results/<YYYYMMDD>/atlas_v1).",
    )
    ap.add_argument("--solver", type=str, default="cadical", help="SAT solver executable.")
    ap.add_argument(
        "--solver-template",
        type=str,
        default=None,
        help="Custom solver command template with {solver},{cnf},{proof},{model}.",
    )
    ap.add_argument("--jobs", type=int, default=1, help="Parallel workers (prune=none only).")
    ap.add_argument("--prune", choices=["none", "monotone"], default="none")
    ap.add_argument(
        "--symmetry",
        choices=["none", "alts"],
        default="none",
        help="Optional post-run equivalence grouping mode.",
    )
    ap.add_argument("--prune-check", action="store_true", help="Verify a fixed sample of pruned cases by re-solving.")
    ap.add_argument("--dry-run", action="store_true", help="Generate CNF/manifest only.")
    ap.add_argument(
        "--emit-proof",
        nargs="?",
        const="always",
        default="unsat-only",
        choices=["unsat-only", "always", "never"],
        help=(
            "Proof emission policy for UNSAT traces. "
            "Use '--emit-proof' (same as always), '--emit-proof unsat-only' (default), or '--emit-proof never'."
        ),
    )
    ap.add_argument(
        "--case-masks",
        type=str,
        default=None,
        help="Optional comma-separated mask integers to run (for smoke/debug).",
    )
    args = ap.parse_args()

    if args.jobs < 1:
        raise ValueError("--jobs must be >= 1")
    if args.prune != "none" and args.jobs != 1:
        print("warning: --jobs is ignored when --prune monotone; using sequential evaluation", file=sys.stderr)

    axiom_universe = parse_axiom_list(args.axiom_universe)
    case_masks = parse_case_masks(args.case_masks, len(axiom_universe))
    cases = make_cases(axiom_universe, case_masks)

    outdir = args.outdir
    outdir.mkdir(parents=True, exist_ok=True)

    summaries, prune_stats, oracle_stats = run_all_cases(
        cases,
        outdir=outdir,
        solver=args.solver,
        solver_template=args.solver_template,
        dry_run=args.dry_run,
        emit_proof_mode=args.emit_proof,
        jobs=args.jobs,
        prune=args.prune,
        prune_check=args.prune_check,
    )

    summaries, symmetry_meta = apply_symmetry_classes(
        summaries,
        outdir=outdir,
        symmetry_mode=args.symmetry,
    )

    status_counts = Counter(str(s.get("status", "UNKNOWN")) for s in summaries)
    atlas: dict[str, object] = {
        "version": "atlas_v1",
        "generated_at_utc": datetime.now(timezone.utc).isoformat(),
        "n": 2,
        "m": 4,
        "axiom_universe": axiom_universe,
        "mask_bit_order": "bit i corresponds to axiom_universe[i], case_id uses this left-to-right bitstring",
        "solver": args.solver,
        "solver_template": args.solver_template,
        "dry_run": args.dry_run,
        "emit_proof": args.emit_proof,
        "jobs": args.jobs,
        "prune": args.prune,
        "prune_check": args.prune_check,
        "symmetry_mode": args.symmetry,
        "outdir": str(outdir),
        "cases_total": len(cases),
        "status_counts": dict(status_counts),
        "prune_stats": prune_stats,
        "oracle_stats": oracle_stats,
        "cases": summaries,
    }
    atlas.update(symmetry_meta)
    atlas_path = outdir / "atlas.json"
    atlas_path.write_text(json.dumps(atlas, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(f"Wrote {atlas_path}")


if __name__ == "__main__":
    main()
