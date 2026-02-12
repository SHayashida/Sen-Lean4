from __future__ import annotations

import itertools
from dataclasses import dataclass


ALT = [0, 1, 2, 3]
PAIR_ORDER = [
    (0, 1),
    (0, 2),
    (0, 3),
    (1, 0),
    (1, 2),
    (1, 3),
    (2, 0),
    (2, 1),
    (2, 3),
    (3, 0),
    (3, 1),
    (3, 2),
]


def _pos_map(rank: tuple[int, ...]) -> dict[int, int]:
    return {a: i for i, a in enumerate(rank)}


@dataclass
class Sen24Schema:
    n: int
    m: int
    include_minlib_selectors: bool

    def __post_init__(self) -> None:
        if self.n != 2 or self.m != 4:
            raise ValueError("Only the Sen base case n=2, m=4 is supported.")

        self.alts: list[int] = ALT[:]
        self.pairs: list[tuple[int, int]] = PAIR_ORDER[:]
        self.pair_idx: dict[tuple[int, int], int] = {
            pair: idx for idx, pair in enumerate(self.pairs)
        }

        self.rankings: list[tuple[int, ...]] = list(
            itertools.permutations(self.alts, len(self.alts))
        )
        self.rank_pos: list[dict[int, int]] = [_pos_map(r) for r in self.rankings]
        self.profiles: list[tuple[int, int]] = [
            (r0, r1)
            for r0 in range(len(self.rankings))
            for r1 in range(len(self.rankings))
        ]

        self.triples: list[tuple[int, int, int]] = [
            (a, b, c)
            for a in self.alts
            for b in self.alts
            for c in self.alts
            if len({a, b, c}) == 3
        ]
        self.quads: list[tuple[int, int, int, int]] = list(
            itertools.permutations(self.alts, len(self.alts))
        )

        self.n_ranks = len(self.rankings)
        self.n_profiles = len(self.profiles)
        self.n_pairs = len(self.pairs)
        self.n_p_vars = self.n_profiles * self.n_pairs

        self.sel0_start: int | None = None
        self.sel0_end: int | None = None
        self.sel1_start: int | None = None
        self.sel1_end: int | None = None
        self.aux_var_range: tuple[int, int] | None = None
        self.n_selector_vars = 0

        if self.include_minlib_selectors:
            aux_start = self.n_p_vars + 1
            aux_end = self.n_p_vars + (2 * self.n_pairs)
            self.sel0_start = aux_start
            self.sel0_end = aux_start + self.n_pairs - 1
            self.sel1_start = self.sel0_end + 1
            self.sel1_end = aux_end
            self.aux_var_range = (aux_start, aux_end)
            self.n_selector_vars = 2 * self.n_pairs

        self.n_vars = self.n_p_vars + self.n_selector_vars

    def var_p(self, p: int, a: int, b: int) -> int:
        return 1 + p * self.n_pairs + self.pair_idx[(a, b)]

    def var_sel0(self, a: int, b: int) -> int:
        if self.sel0_start is None:
            raise ValueError("MINLIB selectors are disabled.")
        return self.sel0_start + self.pair_idx[(a, b)]

    def var_sel1(self, a: int, b: int) -> int:
        if self.sel1_start is None:
            raise ValueError("MINLIB selectors are disabled.")
        return self.sel1_start + self.pair_idx[(a, b)]

    def pref0(self, p: int, a: int, b: int) -> bool:
        r0, _ = self.profiles[p]
        pos0 = self.rank_pos[r0]
        return pos0[a] < pos0[b]

    def pref1(self, p: int, a: int, b: int) -> bool:
        _, r1 = self.profiles[p]
        pos1 = self.rank_pos[r1]
        return pos1[a] < pos1[b]

    def both_prefer(self, p: int, a: int, b: int) -> bool:
        return self.pref0(p, a, b) and self.pref1(p, a, b)

    def manifest_dict(
        self,
        *,
        category_counts: dict[str, int],
        cnf_sha256: str,
        nclauses: int,
        minlib_selected: bool,
    ) -> dict[str, object]:
        manifest: dict[str, object] = {
            "encoding": "sen24",
            "alts": self.alts,
            "pair_order": [list(pair) for pair in self.pairs],
            "ranking_order": "itertools.permutations(ALT,4) lex",
            "profile_order": "p = r0*24 + r1 (r0 major)",
            "nranks": self.n_ranks,
            "nprofiles": self.n_profiles,
            "npairs": self.n_pairs,
            "n_p_vars": self.n_p_vars,
            "nvars": self.n_vars,
            "nclauses": nclauses,
            "category_counts": category_counts,
            "minlib": {
                "mode": "selectors_v1" if minlib_selected else "disabled",
            },
            "p_var_range": [1, self.n_p_vars],
            "aux_var_range": (
                [self.aux_var_range[0], self.aux_var_range[1]]
                if self.aux_var_range is not None
                else None
            ),
            "cnf_sha256": cnf_sha256,
        }
        return manifest

