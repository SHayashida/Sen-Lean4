#!/usr/bin/env python3
from __future__ import annotations

import argparse
import itertools
import json
from collections import Counter
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

    social_true_set = set(p_true)

    def social_bool(profile_idx: int, pair_idx: int) -> bool:
        var = 1 + profile_idx * npairs + pair_idx
        return var in social_true_set

    rankings = list(itertools.permutations([0, 1, 2, 3], 4))
    if len(rankings) != nranks:
        raise ValueError(f"ranking count mismatch: expected {nranks}, got {len(rankings)}")

    pos_maps = [{a: i for i, a in enumerate(r)} for r in rankings]

    total_atoms = nprofiles * npairs
    match_counts = [0, 0]
    pair_support = [0 for _ in range(npairs)]
    signatures: set[tuple[int, ...]] = set()

    for p in range(nprofiles):
        r0_idx = p // nranks
        r1_idx = p % nranks
        pos0 = pos_maps[r0_idx]
        pos1 = pos_maps[r1_idx]
        signature_bits: list[int] = []

        for pair_idx, (a, b) in enumerate(pair_order):
            social = social_bool(p, pair_idx)
            if social:
                pair_support[pair_idx] += 1
            pref0 = pos0[a] < pos0[b]
            pref1 = pos1[a] < pos1[b]
            if social == pref0:
                match_counts[0] += 1
            if social == pref1:
                match_counts[1] += 1
            signature_bits.append(1 if social else 0)

        signatures.add(tuple(signature_bits))

    dictatorship_score_v0 = match_counts[0] / total_atoms if total_atoms > 0 else 0.0
    dictatorship_score_v1 = match_counts[1] / total_atoms if total_atoms > 0 else 0.0
    support_mode, _ = Counter(pair_support).most_common(1)[0]
    neutrality_violation_count = sum(1 for x in pair_support if x != support_mode)
    pair_constancy_score = (
        sum(max(s / nprofiles, 1.0 - (s / nprofiles)) for s in pair_support) / npairs if npairs > 0 else 0.0
    )
    distinct_social_outcomes = len(signatures)
    constant_function = distinct_social_outcomes == 1
    dictator_like_v0 = dictatorship_score_v0 >= 0.98
    dictator_like_v1 = dictatorship_score_v1 >= 0.98

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
    lines.append("## Heuristic triviality scores")
    lines.append("")
    lines.append("- `dictatorship_score_voter0`: fraction of `(p,a,b)` where social bit equals voter0 strict preference.")
    lines.append("- `dictatorship_score_voter1`: fraction of `(p,a,b)` where social bit equals voter1 strict preference.")
    lines.append("- `neutrality_violation_count` (heuristic): ordered pairs whose support differs from modal support.")
    lines.append("- `pair_constancy_score`: average per-pair constancy over profiles (`1.0` means constant by pair).")
    lines.append("- `distinct_social_outcomes`: number of distinct social edge signatures across profiles.")
    lines.append("")
    lines.append(f"- dictatorship_score_voter0: `{dictatorship_score_v0:.4f}`")
    lines.append(f"- dictatorship_score_voter1: `{dictatorship_score_v1:.4f}`")
    lines.append(f"- neutrality_violation_count: `{neutrality_violation_count}` / `{npairs}`")
    lines.append(f"- pair_constancy_score: `{pair_constancy_score:.4f}`")
    lines.append(f"- distinct_social_outcomes: `{distinct_social_outcomes}`")
    lines.append(f"- constant_function_flag: `{constant_function}`")
    lines.append(f"- dictator_like_voter0_flag: `{dictator_like_v0}`")
    lines.append(f"- dictator_like_voter1_flag: `{dictator_like_v1}`")
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
