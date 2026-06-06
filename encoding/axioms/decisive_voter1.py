from __future__ import annotations

from typing import TYPE_CHECKING

if TYPE_CHECKING:
    from encoding.schema import FiniteSchema


name = "decisive_voter1"
category_key = "decisive_voter1"
SUPPORTS_SYMMETRY_ALTS = True


def encode(schema: "FiniteSchema", out_clauses: list[list[int]]) -> None:
    if schema.minlib_mode != "selectors_v1":
        raise ValueError(
            "decisive_voter1 requires legacy selectors_v1 mode and is defined only for the Sen24 base case"
        )

    out_clauses.append([schema.var_sel1(a, b) for (a, b) in schema.pairs])
    for p in range(schema.n_profiles):
        for a, b in schema.pairs:
            lit = schema.var_p(p, a, b) if schema.pref1(p, a, b) else schema.var_p(p, b, a)
            out_clauses.append([-schema.var_sel1(a, b), lit])


def expected_count(schema: "FiniteSchema") -> int:
    if schema.minlib_mode != "selectors_v1":
        return 0
    return 1 + schema.n_profiles * schema.n_pairs
