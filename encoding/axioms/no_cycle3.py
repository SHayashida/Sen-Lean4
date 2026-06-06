from __future__ import annotations

from typing import TYPE_CHECKING

if TYPE_CHECKING:
    from encoding.schema import FiniteSchema


name = "no_cycle3"
category_key = "no_cycle3"
SUPPORTS_SYMMETRY_ALTS = True


def encode(schema: "FiniteSchema", out_clauses: list[list[int]]) -> None:
    for p in range(schema.n_profiles):
        for a, b, c in schema.triples:
            out_clauses.append(
                [-schema.var_p(p, a, b), -schema.var_p(p, b, c), -schema.var_p(p, c, a)]
            )


def expected_count(schema: "FiniteSchema") -> int:
    return schema.n_profiles * len(schema.triples)
