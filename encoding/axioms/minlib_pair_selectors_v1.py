from __future__ import annotations

from typing import TYPE_CHECKING

if TYPE_CHECKING:
    from encoding.schema import FiniteSchema


name = "minlib_pair_selectors_v1"
category_key = "minlib"
SUPPORTS_SYMMETRY_ALTS = True


def encode(schema: "FiniteSchema", out_clauses: list[list[int]]) -> None:
    if schema.minlib_mode != "pair_selectors_v1":
        raise ValueError(
            "parametric MINLIB encoding requires schema.minlib_mode='pair_selectors_v1'"
        )

    out_clauses.append(
        [schema.var_minlib_pair(i, j) for (i, j) in schema.minlib_voter_pairs]
    )

    for i, j in schema.minlib_voter_pairs:
        pair_selector = schema.var_minlib_pair(i, j)
        out_clauses.append(
            [-pair_selector]
            + [schema.var_minlib_decisive(i, a, b) for (a, b) in schema.pairs]
        )
        out_clauses.append(
            [-pair_selector]
            + [schema.var_minlib_decisive(j, a, b) for (a, b) in schema.pairs]
        )

    for voter in schema.voters:
        for a, b in schema.pairs:
            decisive_var = schema.var_minlib_decisive(voter, a, b)
            for p in range(schema.n_profiles):
                social_lit = (
                    schema.var_p(p, a, b)
                    if schema.prefers(p, voter, a, b)
                    else schema.var_p(p, b, a)
                )
                out_clauses.append([-decisive_var, social_lit])


def expected_count(schema: "FiniteSchema") -> int:
    if schema.minlib_mode != "pair_selectors_v1":
        return 0
    return (
        1
        + 2 * len(schema.minlib_voter_pairs)
        + schema.n_voters * schema.n_pairs * schema.n_profiles
    )
