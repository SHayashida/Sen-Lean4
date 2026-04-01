from __future__ import annotations

import itertools
from dataclasses import dataclass
from math import comb


def _pos_map(rank: tuple[int, ...]) -> dict[int, int]:
    return {a: i for i, a in enumerate(rank)}


LEGACY_SEN24_PAIR_ORDER = [
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

LEGACY_MINLIB_MODE = "selectors_v1"
PARAMETRIC_MINLIB_MODE = "pair_selectors_v1"
MINLIB_MODES = {"disabled", LEGACY_MINLIB_MODE, PARAMETRIC_MINLIB_MODE}


@dataclass
class FiniteSchema:
    n: int
    m: int
    minlib_mode: str = "disabled"

    def __post_init__(self) -> None:
        if self.n < 1:
            raise ValueError(f"n must be positive, got {self.n}")
        if self.m < 2:
            raise ValueError(f"m must be at least 2, got {self.m}")
        if self.minlib_mode not in MINLIB_MODES:
            raise ValueError(
                f"unknown minlib mode {self.minlib_mode!r}; expected one of {sorted(MINLIB_MODES)}"
            )
        if self.minlib_mode != "disabled" and self.n < 2:
            raise ValueError("minlib requires at least two voters")
        if self.minlib_mode == LEGACY_MINLIB_MODE and (self.n, self.m) != (2, 4):
            raise ValueError("legacy selectors_v1 MINLIB mode is supported only for Sen24 (n=2, m=4)")

        self.n_voters = self.n
        self.n_alts = self.m
        self.voters: list[int] = list(range(self.n))
        self.alts: list[int] = list(range(self.m))

        self.pairs: list[tuple[int, int]] = [
            (a, b) for a in self.alts for b in self.alts if a != b
        ]
        self.pair_idx: dict[tuple[int, int], int] = {
            pair: idx for idx, pair in enumerate(self.pairs)
        }

        self.rankings: list[tuple[int, ...]] = list(
            itertools.permutations(self.alts, len(self.alts))
        )
        self.rank_pos: list[dict[int, int]] = [_pos_map(r) for r in self.rankings]
        self.profiles: list[tuple[int, ...]] = list(
            itertools.product(range(len(self.rankings)), repeat=self.n_voters)
        )

        self.triples: list[tuple[int, int, int]] = list(
            itertools.permutations(self.alts, 3)
        )
        self.quads: list[tuple[int, int, int, int]] = (
            list(itertools.permutations(self.alts, 4)) if self.m >= 4 else []
        )

        self.n_ranks = len(self.rankings)
        self.n_profiles = len(self.profiles)
        self.n_pairs = len(self.pairs)
        self.n_triples = len(self.triples)
        self.n_quads = len(self.quads)
        self.n_p_vars = self.n_profiles * self.n_pairs

        self.profile_shape = tuple(self.n_ranks for _ in self.voters)
        self.profile_order = (
            f"itertools.product(range(nranks), repeat={self.n_voters}) lex"
        )
        self.ranking_order = f"itertools.permutations(ALT,{self.n_alts}) lex"
        self.triple_order = "itertools.permutations(ALT,3) lex"
        self.quad_order = "itertools.permutations(ALT,4) lex"

        self.aux_var_range: tuple[int, int] | None = None
        self.n_aux_vars = 0

        self.sel0_start: int | None = None
        self.sel0_end: int | None = None
        self.sel1_start: int | None = None
        self.sel1_end: int | None = None

        self.minlib_voter_pairs: list[tuple[int, int]] = []
        self.minlib_voter_pair_idx: dict[tuple[int, int], int] = {}
        self.minlib_pair_selector_start: int | None = None
        self.minlib_pair_selector_end: int | None = None
        self.minlib_decisive_selector_start: int | None = None
        self.minlib_decisive_selector_end: int | None = None

        if self.minlib_mode == LEGACY_MINLIB_MODE:
            aux_start = self.n_p_vars + 1
            aux_end = self.n_p_vars + (2 * self.n_pairs)
            self.sel0_start = aux_start
            self.sel0_end = aux_start + self.n_pairs - 1
            self.sel1_start = self.sel0_end + 1
            self.sel1_end = aux_end
            self.aux_var_range = (aux_start, aux_end)
            self.n_aux_vars = 2 * self.n_pairs
        elif self.minlib_mode == PARAMETRIC_MINLIB_MODE:
            aux_start = self.n_p_vars + 1
            self.minlib_voter_pairs = list(itertools.combinations(self.voters, 2))
            self.minlib_voter_pair_idx = {
                pair: idx for idx, pair in enumerate(self.minlib_voter_pairs)
            }
            pair_selector_count = len(self.minlib_voter_pairs)
            decisive_selector_count = self.n_voters * self.n_pairs
            self.minlib_pair_selector_start = aux_start
            self.minlib_pair_selector_end = aux_start + pair_selector_count - 1
            self.minlib_decisive_selector_start = self.minlib_pair_selector_end + 1
            self.minlib_decisive_selector_end = (
                self.minlib_decisive_selector_start + decisive_selector_count - 1
            )
            self.aux_var_range = (
                aux_start,
                self.minlib_decisive_selector_end,
            )
            self.n_aux_vars = pair_selector_count + decisive_selector_count

        self.n_vars = self.n_p_vars + self.n_aux_vars

    @property
    def is_sen24(self) -> bool:
        return (self.n_voters, self.n_alts) == (2, 4)

    def var_p(self, p: int, a: int, b: int) -> int:
        return 1 + p * self.n_pairs + self.pair_idx[(a, b)]

    def var_sel0(self, a: int, b: int) -> int:
        if self.sel0_start is None:
            raise ValueError("legacy MINLIB selectors are disabled")
        return self.sel0_start + self.pair_idx[(a, b)]

    def var_sel1(self, a: int, b: int) -> int:
        if self.sel1_start is None:
            raise ValueError("legacy MINLIB selectors are disabled")
        return self.sel1_start + self.pair_idx[(a, b)]

    def var_minlib_pair(self, i: int, j: int) -> int:
        if self.minlib_pair_selector_start is None:
            raise ValueError("parametric MINLIB pair selectors are disabled")
        pair = (i, j) if i < j else (j, i)
        return self.minlib_pair_selector_start + self.minlib_voter_pair_idx[pair]

    def var_minlib_decisive(self, voter: int, a: int, b: int) -> int:
        if self.minlib_decisive_selector_start is None:
            raise ValueError("parametric MINLIB decisive selectors are disabled")
        return (
            self.minlib_decisive_selector_start
            + voter * self.n_pairs
            + self.pair_idx[(a, b)]
        )

    def profile_rank_index(self, p: int, voter: int) -> int:
        return self.profiles[p][voter]

    def profile_rank(self, p: int, voter: int) -> tuple[int, ...]:
        return self.rankings[self.profile_rank_index(p, voter)]

    def prefers(self, p: int, voter: int, a: int, b: int) -> bool:
        rank_idx = self.profile_rank_index(p, voter)
        return self.rank_pos[rank_idx][a] < self.rank_pos[rank_idx][b]

    def pref0(self, p: int, a: int, b: int) -> bool:
        return self.prefers(p, 0, a, b)

    def pref1(self, p: int, a: int, b: int) -> bool:
        return self.prefers(p, 1, a, b)

    def all_voters_prefer(self, p: int, a: int, b: int) -> bool:
        return all(self.prefers(p, voter, a, b) for voter in self.voters)

    def both_prefer(self, p: int, a: int, b: int) -> bool:
        return self.all_voters_prefer(p, a, b)

    def minlib_support_clause_length(self) -> int:
        return 1 + self.n_pairs

    def minlib_pair_selector_count(self) -> int:
        return comb(self.n_voters, 2)

    def minlib_decisive_selector_count(self) -> int:
        return self.n_voters * self.n_pairs

    def manifest_dict(
        self,
        *,
        axiom_names: list[str],
        category_counts: dict[str, int],
        cnf_sha256: str,
        nclauses: int,
    ) -> dict[str, object]:
        legacy_axioms = {"asymm", "un", "minlib", "no_cycle3", "no_cycle4"}
        uses_legacy_manifest = (
            self.is_sen24
            and self.minlib_mode in {"disabled", LEGACY_MINLIB_MODE}
            and set(axiom_names).issubset(legacy_axioms)
        )
        if uses_legacy_manifest:
            return self._legacy_manifest_dict(
                category_counts=category_counts,
                cnf_sha256=cnf_sha256,
                nclauses=nclauses,
            )
        return self._parametric_manifest_dict(
            axiom_names=axiom_names,
            category_counts=category_counts,
            cnf_sha256=cnf_sha256,
            nclauses=nclauses,
        )

    def _legacy_manifest_dict(
        self,
        *,
        category_counts: dict[str, int],
        cnf_sha256: str,
        nclauses: int,
    ) -> dict[str, object]:
        return {
            "encoding": "sen24",
            "alts": self.alts,
            "pair_order": [list(pair) for pair in self.pairs],
            "ranking_order": self.ranking_order,
            "profile_order": "p = r0*24 + r1 (r0 major)",
            "nranks": self.n_ranks,
            "nprofiles": self.n_profiles,
            "npairs": self.n_pairs,
            "n_p_vars": self.n_p_vars,
            "nvars": self.n_vars,
            "nclauses": nclauses,
            "category_counts": category_counts,
            "minlib": {
                "mode": self.minlib_mode,
            },
            "p_var_range": [1, self.n_p_vars],
            "aux_var_range": (
                [self.aux_var_range[0], self.aux_var_range[1]]
                if self.aux_var_range is not None
                else None
            ),
            "cnf_sha256": cnf_sha256,
        }

    def _parametric_manifest_dict(
        self,
        *,
        axiom_names: list[str],
        category_counts: dict[str, int],
        cnf_sha256: str,
        nclauses: int,
    ) -> dict[str, object]:
        minlib: dict[str, object] = {"mode": self.minlib_mode}
        if self.minlib_mode == PARAMETRIC_MINLIB_MODE:
            minlib.update(
                {
                    "pair_selector_order": [list(pair) for pair in self.minlib_voter_pairs],
                    "pair_selector_var_range": [
                        self.minlib_pair_selector_start,
                        self.minlib_pair_selector_end,
                    ],
                    "pair_selector_count": self.minlib_pair_selector_count(),
                    "decisive_voters": self.voters,
                    "decisive_var_range": [
                        self.minlib_decisive_selector_start,
                        self.minlib_decisive_selector_end,
                    ],
                    "decisive_selector_count": self.minlib_decisive_selector_count(),
                }
            )

        return {
            "encoding": "finite_schema_v1",
            "schema_version": 1,
            "n_voters": self.n_voters,
            "n_alts": self.n_alts,
            "voters": self.voters,
            "alts": self.alts,
            "pair_order": [list(pair) for pair in self.pairs],
            "ranking_order": self.ranking_order,
            "profile_order": self.profile_order,
            "triple_order": self.triple_order,
            "quad_order": self.quad_order,
            "nranks": self.n_ranks,
            "nprofiles": self.n_profiles,
            "npairs": self.n_pairs,
            "ntriples": self.n_triples,
            "nquads": self.n_quads,
            "n_p_vars": self.n_p_vars,
            "nvars": self.n_vars,
            "nclauses": nclauses,
            "axioms": axiom_names,
            "category_counts": category_counts,
            "minlib": minlib,
            "p_var_range": [1, self.n_p_vars],
            "aux_var_range": (
                [self.aux_var_range[0], self.aux_var_range[1]]
                if self.aux_var_range is not None
                else None
            ),
            "cnf_sha256": cnf_sha256,
        }


def resolve_minlib_mode(
    *,
    n: int,
    m: int,
    minlib_enabled: bool,
    requested_mode: str = "auto",
) -> str:
    if requested_mode not in {"auto", LEGACY_MINLIB_MODE, PARAMETRIC_MINLIB_MODE}:
        raise ValueError(
            "requested minlib mode must be one of 'auto', "
            f"'{LEGACY_MINLIB_MODE}', '{PARAMETRIC_MINLIB_MODE}'"
        )
    if not minlib_enabled:
        return "disabled"
    if requested_mode == "auto":
        if (n, m) == (2, 4):
            return LEGACY_MINLIB_MODE
        return PARAMETRIC_MINLIB_MODE
    if requested_mode == LEGACY_MINLIB_MODE and (n, m) != (2, 4):
        raise ValueError(
            "selectors_v1 is a Sen24 compatibility mode and cannot be used outside (n=2, m=4)"
        )
    return requested_mode


def Sen24Schema(
    *,
    n: int = 2,
    m: int = 4,
    include_minlib_selectors: bool | None = None,
    minlib_mode: str | None = None,
) -> FiniteSchema:
    if include_minlib_selectors is not None and minlib_mode is not None:
        raise ValueError("specify either include_minlib_selectors or minlib_mode, not both")
    if include_minlib_selectors is not None:
        resolved_mode = LEGACY_MINLIB_MODE if include_minlib_selectors else "disabled"
    else:
        resolved_mode = minlib_mode or "disabled"
    return FiniteSchema(n=n, m=m, minlib_mode=resolved_mode)
