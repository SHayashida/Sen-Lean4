#!/usr/bin/env python3
from __future__ import annotations

import argparse
import itertools
import json
from pathlib import Path


def load_json(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def fmt_perm(perm: tuple[int, ...]) -> str:
    return "[" + ",".join(str(x) for x in perm) + "]"


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--case-dir", type=Path, required=True, help="Case directory with model.json + manifest.")
    ap.add_argument("--max-profiles", type=int, default=20, help="Maximum sample profiles in rule.md.")
    args = ap.parse_args()

    case_dir = args.case_dir
    summary_path = case_dir / "summary.json"
    manifest_path = case_dir / "sen24.manifest.json"
    model_path = case_dir / "model.json"
    out_path = case_dir / "rule.md"

    if not manifest_path.exists():
        raise FileNotFoundError(f"missing manifest: {manifest_path}")
    if not model_path.exists():
        raise FileNotFoundError(f"missing model: {model_path}")

    summary = load_json(summary_path) if summary_path.exists() else {}
    manifest = load_json(manifest_path)
    model = load_json(model_path)

    n_p_vars = int(manifest["n_p_vars"])
    npairs = int(manifest["npairs"])
    nprofiles = int(manifest["nprofiles"])
    nranks = int(manifest["nranks"])
    pair_order = [tuple(x) for x in manifest["pair_order"]]
    true_vars = sorted(int(v) for v in model.get("true_vars", []))

    p_true = [v for v in true_vars if 1 <= v <= n_p_vars]
    aux_true = [v for v in true_vars if v > n_p_vars]

    by_profile: dict[int, list[tuple[int, int]]] = {}
    for var in p_true:
        idx = var - 1
        p = idx // npairs
        pair_idx = idx % npairs
        edge = pair_order[pair_idx]
        by_profile.setdefault(p, []).append(edge)
    for p in by_profile:
        by_profile[p] = sorted(by_profile[p])

    rankings = list(itertools.permutations([0, 1, 2, 3], 4))
    if len(rankings) != nranks:
        raise ValueError(f"ranking count mismatch: expected {nranks}, got {len(rankings)}")

    profile_ids = list(range(min(nprofiles, max(0, args.max_profiles))))
    lines: list[str] = []
    lines.append("# Human-readable SAT rule sketch")
    lines.append("")
    lines.append(f"- case_id: `{summary.get('case_id', case_dir.name)}`")
    lines.append(f"- status: `{summary.get('status', 'SAT')}`")
    lines.append(f"- axioms_on: `{', '.join(summary.get('axioms_on', []))}`")
    lines.append(f"- model true vars: `{len(true_vars)}` (p-vars: `{len(p_true)}`, aux-vars: `{len(aux_true)}`)")
    lines.append("")
    lines.append("## Variable semantics")
    lines.append("")
    lines.append("- `p_var` (`1..n_p_vars`): social strict preference bit `P[p,a,b]`.")
    lines.append("- `aux_var` (`n_p_vars+1..`): auxiliary encoding bits (e.g., MINLIB selectors).")
    lines.append("- profile index convention: `p = r0 * nranks + r1`.")
    lines.append("")
    lines.append("## Profile samples")
    lines.append("")
    lines.append(f"Showing first `{len(profile_ids)}` profiles (out of `{nprofiles}`).")
    lines.append("")
    for p in profile_ids:
        r0_idx = p // nranks
        r1_idx = p % nranks
        r0 = rankings[r0_idx]
        r1 = rankings[r1_idx]
        edges = by_profile.get(p, [])
        edges_text = ", ".join(f"{a}>{b}" for (a, b) in edges) if edges else "(none)"
        lines.append(
            f"- `p={p}` (`r0={fmt_perm(r0)}`, `r1={fmt_perm(r1)}`) -> social edges: {edges_text}"
        )

    out_path.write_text("\n".join(lines).rstrip() + "\n", encoding="utf-8")
    print(f"Wrote {out_path}")


if __name__ == "__main__":
    main()

