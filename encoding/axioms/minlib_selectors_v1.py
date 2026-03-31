from __future__ import annotations

from typing import TYPE_CHECKING

if TYPE_CHECKING:
    from encoding.schema import FiniteSchema


name = "minlib_selectors_v1"
category_key = "minlib"
SUPPORTS_SYMMETRY_ALTS = True


def encode(schema: "FiniteSchema", out_clauses: list[list[int]]) -> None:
    if schema.minlib_mode != "selectors_v1":
        raise ValueError(
            f"legacy MINLIB encoding requires schema.minlib_mode='selectors_v1', got {schema.minlib_mode!r}"
        )

    out_clauses.append([schema.var_sel0(a, b) for (a, b) in schema.pairs])
    out_clauses.append([schema.var_sel1(a, b) for (a, b) in schema.pairs])

    for p in range(schema.n_profiles):
        for a, b in schema.pairs:
            lit0 = schema.var_p(p, a, b) if schema.pref0(p, a, b) else schema.var_p(p, b, a)
            out_clauses.append([-schema.var_sel0(a, b), lit0])

            lit1 = schema.var_p(p, a, b) if schema.pref1(p, a, b) else schema.var_p(p, b, a)
            out_clauses.append([-schema.var_sel1(a, b), lit1])


def expected_count(schema: "FiniteSchema") -> int:
    if schema.minlib_mode != "selectors_v1":
        return 0
    return 2 + 2 * schema.n_profiles * schema.n_pairs
