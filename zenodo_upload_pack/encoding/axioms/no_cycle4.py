from __future__ import annotations

from typing import TYPE_CHECKING

if TYPE_CHECKING:
    from encoding.schema import Sen24Schema


name = "no_cycle4"
category_key = "no_cycle4"
SUPPORTS_SYMMETRY_ALTS = True


def encode(schema: "Sen24Schema", out_clauses: list[list[int]]) -> None:
    for p in range(schema.n_profiles):
        for a, b, c, d in schema.quads:
            out_clauses.append(
                [
                    -schema.var_p(p, a, b),
                    -schema.var_p(p, b, c),
                    -schema.var_p(p, c, d),
                    -schema.var_p(p, d, a),
                ]
            )


def expected_count(schema: "Sen24Schema") -> int:
    return schema.n_profiles * len(schema.quads)
