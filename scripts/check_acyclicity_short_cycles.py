#!/usr/bin/env python3
"""Exhaustively check the sen24 short-cycle bridge on four alternatives.

For the fixed 4-alternative domain, the CNF uses `NO_CYCLE3` and `NO_CYCLE4`
instead of encoding `Acyclic` directly. This script checks the exact finite
bridge used in the paper:

  for every asymmetric relation on 4 alternatives,
  Acyclic <-> (no directed 3-cycle and no directed 4-cycle).

The result is an audited finite-domain fact for sen24. It is not claimed as a
general theorem for arbitrary domain sizes.
"""

from __future__ import annotations

import argparse
import itertools
import json
import sys
from typing import Iterable

ALTS = tuple(range(4))
ALL_EDGES = tuple((a, b) for a in ALTS for b in ALTS)


def relation_from_mask(mask: int) -> set[tuple[int, int]]:
    return {edge for bit, edge in enumerate(ALL_EDGES) if mask & (1 << bit)}


def is_asymmetric(relation: set[tuple[int, int]]) -> bool:
    return all((b, a) not in relation for (a, b) in relation)


def transitive_closure(relation: set[tuple[int, int]]) -> dict[int, set[int]]:
    reach = {a: set() for a in ALTS}
    for a, b in relation:
        reach[a].add(b)

    changed = True
    while changed:
        changed = False
        for a in ALTS:
            expanded = set(reach[a])
            for b in list(reach[a]):
                expanded.update(reach[b])
            if expanded != reach[a]:
                reach[a] = expanded
                changed = True
    return reach


def is_acyclic(relation: set[tuple[int, int]]) -> bool:
    closure = transitive_closure(relation)
    return all(a not in closure[a] for a in ALTS)


def has_cycle_of_length(relation: set[tuple[int, int]], length: int) -> bool:
    for nodes in itertools.permutations(ALTS, length):
        if all((nodes[i], nodes[(i + 1) % length]) in relation for i in range(length)):
            return True
    return False


def relation_to_sorted_edges(relation: Iterable[tuple[int, int]]) -> list[list[int]]:
    return [[a, b] for (a, b) in sorted(relation)]


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--json-out",
        help="Optional path to write the machine-readable summary.",
    )
    args = parser.parse_args()

    counterexamples: list[dict[str, object]] = []
    asymmetric_relations = 0
    total_relations = 1 << len(ALL_EDGES)

    for mask in range(total_relations):
        relation = relation_from_mask(mask)
        if not is_asymmetric(relation):
            continue
        asymmetric_relations += 1

        acyclic = is_acyclic(relation)
        no_short_cycles = (
            not has_cycle_of_length(relation, 3)
            and not has_cycle_of_length(relation, 4)
        )
        if acyclic != no_short_cycles:
            counterexamples.append(
                {
                    "mask": mask,
                    "edges": relation_to_sorted_edges(relation),
                    "acyclic": acyclic,
                    "no_cycle3_or_4": no_short_cycles,
                }
            )

    summary = {
        "domain_size": len(ALTS),
        "relations_total": total_relations,
        "asymmetric_relations_checked": asymmetric_relations,
        "property": (
            "For asymmetric relations on four alternatives, "
            "Acyclic iff forbidding directed 3-cycles and 4-cycles."
        ),
        "counterexample_count": len(counterexamples),
        "status": "ok" if not counterexamples else "counterexamples_found",
        "counterexamples": counterexamples[:5],
    }

    rendered = json.dumps(summary, indent=2, sort_keys=True)
    if args.json_out:
        with open(args.json_out, "w", encoding="utf-8") as handle:
            handle.write(rendered)
            handle.write("\n")
    print(rendered)
    return 0 if not counterexamples else 1


if __name__ == "__main__":
    sys.exit(main())
