from __future__ import annotations

from typing import TYPE_CHECKING

if TYPE_CHECKING:
    from encoding.schema import Sen24Schema


name = "un"
category_key = "un"
SUPPORTS_SYMMETRY_ALTS = True


def encode(schema: "Sen24Schema", out_clauses: list[list[int]]) -> None:
    for p in range(schema.n_profiles):
        for a, b in schema.pairs:
            if schema.both_prefer(p, a, b):
                out_clauses.append([schema.var_p(p, a, b)])


def expected_count(schema: "Sen24Schema") -> int:
    count = 0
    for p in range(schema.n_profiles):
        for a, b in schema.pairs:
            if schema.both_prefer(p, a, b):
                count += 1
    return count
