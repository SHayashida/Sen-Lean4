#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import shlex
import subprocess
import sys
import time
from collections import Counter
from concurrent.futures import ThreadPoolExecutor, as_completed
from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

from gen_dimacs import run_generation  # noqa: E402


SUPPORTED_AXIOMS = ["asymm", "un", "minlib", "no_cycle3", "no_cycle4"]


@dataclass(frozen=True)
class CaseSpec:
    mask: int
    bitstring: str
    case_id: str
    axioms_on: list[str]
    axioms_off: list[str]


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
            if lit > 0 and lit <= nvars:
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
            if lit > 0 and lit <= nvars:
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

    if dry_run:
        status = "UNKNOWN"
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

        merged_duration = sum(float(at.get("duration_sec", 0.0)) for at in attempts)
        duration_sec = merged_duration
        command = list(attempts[-1]["cmd"]) if attempts and attempts[-1].get("cmd") is not None else None
        return_code = attempts[-1].get("return_code") if attempts else None
        if attempts and attempts[-1].get("error") is not None:
            solver_error = str(attempts[-1].get("error"))

        _write_solver_log(
            solver_log_path,
            dry_run=False,
            attempts=attempts,
        )

        if status == "SAT":
            stdout_all = "\n".join(str(at.get("stdout", "")) for at in attempts)
            model_observed = _has_v_lines(stdout_all)
            model_true_vars = _parse_true_vars_from_v_lines(stdout_all, int(manifest["nvars"]))
            if model_path.exists():
                model_text = model_path.read_text(encoding="utf-8", errors="ignore")
                model_observed = model_observed or _has_v_lines(model_text)
                if not model_true_vars:
                    model_true_vars = _parse_true_vars_from_model_file(
                        model_text,
                        int(manifest["nvars"]),
                    )
        if status == "UNSAT" and proof_path.exists():
            proof_file = proof_path.name

    if status == "SAT" and model_observed:
        model_json_path.write_text(
            json.dumps(
                {
                    "nvars": int(manifest["nvars"]),
                    "n_true": len(model_true_vars),
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
        proof_cmd = None
        for at in reversed(attempts):
            if bool(at.get("with_proof")) and at.get("cmd") is not None:
                proof_cmd = " ".join(shlex.quote(str(x)) for x in list(at["cmd"]))
                break
        proof = {
            "format": "lrat",
            "path": proof_file,
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
        "files": {
            "cnf": cnf_path.name,
            "manifest": manifest_path.name,
            "solver_log": solver_log_path.name,
            "summary": summary_path.name,
        },
        "manifest": {
            "nvars": int(manifest["nvars"]),
            "nclauses": int(manifest["nclauses"]),
            "category_counts": manifest["category_counts"],
            "minlib": manifest["minlib"],
        },
    }
    summary_path.write_text(json.dumps(summary, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return summary


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
) -> list[dict[str, object]]:
    if prune == "none":
        if jobs <= 1:
            return [
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
        return [results_by_id[case.case_id] for case in cases]

    if prune != "monotone":
        raise ValueError(f"Unsupported prune mode: {prune}")

    ordered_cases = sorted(cases, key=lambda c: (bin(c.mask).count("1"), c.mask))
    results_by_mask: dict[int, dict[str, object]] = {}
    unsat_masks: list[int] = []

    for case in ordered_cases:
        pruned_by = next((m for m in unsat_masks if (m & case.mask) == m and m != case.mask), None)
        if pruned_by is not None:
            case_dir = outdir / case.case_id
            case_dir.mkdir(parents=True, exist_ok=True)
            summary = {
                "case_id": case.case_id,
                "mask_int": case.mask,
                "mask_bits": case.bitstring,
                "axioms_on": case.axioms_on,
                "axioms_off": case.axioms_off,
                "status": "PRUNED",
                "pruned_by_mask": pruned_by,
                "dry_run": dry_run,
                "solver": solver,
            }
            (case_dir / "solver.log").write_text(
                f"pruned: monotone UNSAT ancestor mask={pruned_by}\n",
                encoding="utf-8",
            )
            (case_dir / "summary.json").write_text(
                json.dumps(summary, indent=2, sort_keys=True) + "\n",
                encoding="utf-8",
            )
            results_by_mask[case.mask] = summary
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
        if summary.get("status") == "UNSAT":
            unsat_masks.append(case.mask)

    return [results_by_mask[case.mask] for case in cases]


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

    axiom_universe = parse_axiom_list(args.axiom_universe)
    case_masks = parse_case_masks(args.case_masks, len(axiom_universe))
    cases = make_cases(axiom_universe, case_masks)

    outdir = args.outdir
    outdir.mkdir(parents=True, exist_ok=True)

    summaries = run_all_cases(
        cases,
        outdir=outdir,
        solver=args.solver,
        solver_template=args.solver_template,
        dry_run=args.dry_run,
        emit_proof_mode=args.emit_proof,
        jobs=args.jobs,
        prune=args.prune,
    )

    status_counts = Counter(str(s.get("status", "UNKNOWN")) for s in summaries)
    atlas = {
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
        "outdir": str(outdir),
        "cases_total": len(cases),
        "status_counts": dict(status_counts),
        "cases": summaries,
    }
    atlas_path = outdir / "atlas.json"
    atlas_path.write_text(json.dumps(atlas, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(f"Wrote {atlas_path}")


if __name__ == "__main__":
    main()
