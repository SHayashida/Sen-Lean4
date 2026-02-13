#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import re
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Any


@dataclass(frozen=True)
class CNF:
    nvars: int
    nclauses: int
    clauses: list[tuple[int, ...]]


def parse_dimacs(path: Path) -> CNF:
    nvars: int | None = None
    nclauses_declared: int | None = None
    clauses: list[tuple[int, ...]] = []
    current: list[int] = []

    for raw in path.read_text(encoding="utf-8", errors="ignore").splitlines():
        line = raw.strip()
        if not line or line.startswith("c"):
            continue
        if line.startswith("p"):
            parts = line.split()
            if len(parts) != 4 or parts[1] != "cnf":
                raise ValueError(f"invalid DIMACS header: {line}")
            nvars = int(parts[2])
            nclauses_declared = int(parts[3])
            continue

        for token in line.split():
            lit = int(token)
            if lit == 0:
                clauses.append(tuple(current))
                current = []
            else:
                current.append(lit)

    if current:
        raise ValueError("DIMACS ended with unterminated clause (missing trailing 0)")
    if nvars is None or nclauses_declared is None:
        raise ValueError("missing DIMACS header")
    if len(clauses) != nclauses_declared:
        raise ValueError(
            f"clause count mismatch: header={nclauses_declared} parsed={len(clauses)}"
        )

    return CNF(nvars=nvars, nclauses=nclauses_declared, clauses=clauses)


def _assignment_from_literals(literals: list[int], nvars: int) -> dict[int, bool]:
    assignment: dict[int, bool] = {}
    for lit in literals:
        var = abs(int(lit))
        if var == 0 or var > nvars:
            continue
        value = int(lit) > 0
        prev = assignment.get(var)
        if prev is not None and prev != value:
            raise ValueError(f"conflicting literal assignments for var {var}")
        assignment[var] = value
    return assignment


def load_assignment(model: dict[str, Any], nvars: int) -> dict[int, bool]:
    if isinstance(model.get("assignment"), dict):
        assignment: dict[int, bool] = {}
        for key, raw_value in model["assignment"].items():
            var = int(key)
            if var < 1 or var > nvars:
                continue
            if isinstance(raw_value, bool):
                assignment[var] = raw_value
            elif isinstance(raw_value, (int, float)):
                assignment[var] = bool(raw_value)
            elif isinstance(raw_value, str):
                lowered = raw_value.strip().lower()
                if lowered in {"1", "true", "t", "yes"}:
                    assignment[var] = True
                elif lowered in {"0", "false", "f", "no"}:
                    assignment[var] = False
                else:
                    raise ValueError(f"cannot parse assignment value for var {var}: {raw_value}")
            else:
                raise ValueError(f"unsupported assignment value type for var {var}: {type(raw_value)}")
        return assignment

    if isinstance(model.get("literals"), list):
        literals = [int(x) for x in model["literals"]]
        return _assignment_from_literals(literals, nvars)

    if isinstance(model.get("true_vars"), list):
        true_vars = [int(v) for v in model["true_vars"]]
        assignment = {var: False for var in range(1, nvars + 1)}
        for var in true_vars:
            if 1 <= var <= nvars:
                assignment[var] = True
        return assignment

    raise ValueError("model does not contain assignment/true_vars/literals")


def validate_witness(
    *,
    cnf_path: Path,
    model_path: Path,
    strict_unassigned: bool = True,
) -> dict[str, Any]:
    cnf = parse_dimacs(cnf_path)
    model = json.loads(model_path.read_text(encoding="utf-8"))
    assignment = load_assignment(model, cnf.nvars)

    unassigned_vars = [var for var in range(1, cnf.nvars + 1) if var not in assignment]

    satisfied_count = 0
    first_unsat_clause_idx: int | None = None
    for idx, clause in enumerate(cnf.clauses, start=1):
        clause_sat = False
        for lit in clause:
            var = abs(lit)
            value = assignment.get(var)
            if value is None:
                continue
            if (lit > 0 and value) or (lit < 0 and not value):
                clause_sat = True
                break
        if clause_sat:
            satisfied_count += 1
        elif first_unsat_clause_idx is None:
            first_unsat_clause_idx = idx

    ok = first_unsat_clause_idx is None
    if strict_unassigned and unassigned_vars:
        ok = False

    report = {
        "ok": ok,
        "strict_unassigned": strict_unassigned,
        "num_vars": cnf.nvars,
        "num_clauses": cnf.nclauses,
        "satisfied_clauses": satisfied_count,
        "first_unsat_clause_idx": first_unsat_clause_idx,
        "unassigned_count": len(unassigned_vars),
        "first_unassigned_vars": unassigned_vars[:20],
    }
    return report


def main() -> None:
    ap = argparse.ArgumentParser(description="Validate SAT witness assignment against DIMACS CNF")
    ap.add_argument("--cnf", type=Path, required=True, help="Path to DIMACS CNF file")
    ap.add_argument("--model", type=Path, required=True, help="Path to model.json file")
    ap.add_argument(
        "--strict-unassigned",
        dest="strict_unassigned",
        action="store_true",
        default=True,
        help="Fail if any variable is unassigned (default: true)",
    )
    ap.add_argument(
        "--allow-unassigned",
        dest="strict_unassigned",
        action="store_false",
        help="Allow unassigned variables",
    )
    ap.add_argument("--out", type=Path, default=None, help="Optional path to write validation report JSON")
    args = ap.parse_args()

    try:
        report = validate_witness(
            cnf_path=args.cnf,
            model_path=args.model,
            strict_unassigned=args.strict_unassigned,
        )
    except Exception as ex:
        error_report = {
            "ok": False,
            "error": str(ex),
            "cnf": str(args.cnf),
            "model": str(args.model),
        }
        if args.out is not None:
            args.out.write_text(json.dumps(error_report, indent=2, sort_keys=True) + "\n", encoding="utf-8")
        print(json.dumps(error_report, indent=2, sort_keys=True))
        raise SystemExit(1)

    if args.out is not None:
        args.out.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n", encoding="utf-8")

    print(json.dumps(report, indent=2, sort_keys=True))
    raise SystemExit(0 if report["ok"] else 2)


if __name__ == "__main__":
    main()
