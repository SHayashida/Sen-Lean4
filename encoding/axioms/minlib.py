from __future__ import annotations

from typing import TYPE_CHECKING

from . import minlib_pair_selectors_v1, minlib_selectors_v1

if TYPE_CHECKING:
    from encoding.schema import FiniteSchema


name = "minlib"
category_key = "minlib"
SUPPORTS_SYMMETRY_ALTS = True


def encode(schema: "FiniteSchema", out_clauses: list[list[int]]) -> None:
    if schema.minlib_mode == "disabled":
        raise ValueError("MINLIB encoding requested, but minlib_mode is disabled in schema.")
    if schema.minlib_mode == "selectors_v1":
        minlib_selectors_v1.encode(schema, out_clauses)
        return
    if schema.minlib_mode == "pair_selectors_v1":
        minlib_pair_selectors_v1.encode(schema, out_clauses)
        return
    raise ValueError(f"unsupported MINLIB mode: {schema.minlib_mode!r}")


def expected_count(schema: "FiniteSchema") -> int:
    if schema.minlib_mode == "disabled":
        return 0
    if schema.minlib_mode == "selectors_v1":
        return minlib_selectors_v1.expected_count(schema)
    if schema.minlib_mode == "pair_selectors_v1":
        return minlib_pair_selectors_v1.expected_count(schema)
    raise ValueError(f"unsupported MINLIB mode: {schema.minlib_mode!r}")
