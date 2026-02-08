#!/usr/bin/env python3
"""
Mechanical auditor for `Certificates/sen24.cnf` (Sen base case, n=2 voters, m=4 alts).

This script:
  - parses DIMACS CNF (comments ignored),
  - validates header / literal ranges / clause well-formedness,
  - recomputes the expected clauses for each category from the encoding spec,
  - compares expected vs observed (as multisets, i.e. including duplicates),
  - prints a category report and fails with non-zero exit code on mismatch.

Usage:
  python3 scripts/check_sen24_cnf.py Certificates/sen24.cnf \
    --manifest Certificates/sen24.manifest.json

Flags:
  --strict-duplicates   Fail on duplicate literals in a clause (default: warn + de-dup)
  --fail-on-tautology   Fail on tautological clauses (default: warn + ignore)
"""

from __future__ import annotations

import argparse
import hashlib
import itertools
import json
import sys
from collections import Counter
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable


SPEC_ALT = [0, 1, 2, 3]
SPEC_PAIRS = [
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


class AuditError(RuntimeError):
    pass


def sha256_file(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as f:
        for chunk in iter(lambda: f.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


@dataclass(frozen=True)
class Manifest:
    alts: list[int]
    pair_order: list[tuple[int, int]]
    nranks: int
    nprofiles: int
    npairs: int
    n_p_vars: int
    nvars: int
    nclauses: int
    category_counts: dict[str, int]
    minlib_mode: str
    p_var_range: tuple[int, int]
    aux_var_range: tuple[int, int] | None
    cnf_sha256: str


def load_manifest(path: Path, cnf_path: Path) -> Manifest:
    obj = json.loads(path.read_text(encoding="utf-8"))
    if obj.get("encoding") != "sen24":
        raise AuditError(f"manifest.encoding must be 'sen24', got {obj.get('encoding')!r}")

    cnf_sha = sha256_file(cnf_path)
    if "cnf_sha256" in obj and obj["cnf_sha256"] != cnf_sha:
        raise AuditError(
            "manifest.cnf_sha256 does not match CNF file: "
            f"{obj['cnf_sha256']} (manifest) vs {cnf_sha} (file)"
        )

    alts = list(obj["alts"])
    pair_order = [tuple(x) for x in obj["pair_order"]]
    aux_range = None
    if obj.get("aux_var_range") is not None:
        aux_range = (int(obj["aux_var_range"][0]), int(obj["aux_var_range"][1]))
    return Manifest(
        alts=alts,
        pair_order=pair_order,
        nranks=int(obj["nranks"]),
        nprofiles=int(obj["nprofiles"]),
        npairs=int(obj["npairs"]),
        n_p_vars=int(obj["n_p_vars"]),
        nvars=int(obj["nvars"]),
        nclauses=int(obj["nclauses"]),
        category_counts={k: int(v) for k, v in obj["category_counts"].items()},
        minlib_mode=str(obj.get("minlib", {}).get("mode", "")),
        p_var_range=(int(obj["p_var_range"][0]), int(obj["p_var_range"][1])),
        aux_var_range=aux_range,
        cnf_sha256=cnf_sha,
    )


def parse_dimacs(path: Path) -> tuple[int, int, list[tuple[int, list[int]]]]:
    nvars = None
    nclauses = None
    clauses: list[tuple[int, list[int]]] = []

    for lineno, raw in enumerate(path.read_text(encoding="utf-8").splitlines(), start=1):
        line = raw.strip()
        if not line or line.startswith("c"):
            continue
        if line.startswith("p "):
            parts = line.split()
            if parts[:2] != ["p", "cnf"] or len(parts) != 4:
                raise AuditError(f"{path}:{lineno}: malformed header: {raw!r}")
            nvars = int(parts[2])
            nclauses = int(parts[3])
            continue

        if nvars is None or nclauses is None:
            raise AuditError(f"{path}:{lineno}: clause before header")
        try:
            ints = [int(x) for x in line.split()]
        except ValueError as e:
            raise AuditError(f"{path}:{lineno}: non-integer literal: {raw!r}") from e
        if not ints:
            raise AuditError(f"{path}:{lineno}: empty line after stripping")
        if ints[-1] != 0:
            raise AuditError(f"{path}:{lineno}: clause does not end with 0: {raw!r}")
        if 0 in ints[:-1]:
            raise AuditError(f"{path}:{lineno}: clause contains 0 before terminator: {raw!r}")
        lits = ints[:-1]
        for lit in lits:
            if lit == 0:
                raise AuditError(f"{path}:{lineno}: literal 0 in clause: {raw!r}")
            if nvars is not None and abs(lit) > nvars:
                raise AuditError(
                    f"{path}:{lineno}: literal {lit} out of range for nvars={nvars}"
                )
        clauses.append((lineno, lits))

    if nvars is None or nclauses is None:
        raise AuditError(f"{path}: missing 'p cnf' header")
    if len(clauses) != nclauses:
        raise AuditError(
            f"{path}: header says {nclauses} clauses but parsed {len(clauses)}"
        )
    return nvars, nclauses, clauses


def canon_clause(
    lits: list[int], *, path: Path, lineno: int, strict_duplicates: bool
) -> tuple[tuple[int, ...], bool, bool]:
    seen = set()
    had_dups = False
    for lit in lits:
        if lit in seen:
            had_dups = True
            if strict_duplicates:
                raise AuditError(f"{path}:{lineno}: duplicate literal {lit} in clause {lits}")
            continue
        seen.add(lit)
    taut = any((-lit) in seen for lit in seen)
    return tuple(sorted(seen)), taut, had_dups


def all_rankings(alts: list[int]) -> list[tuple[int, ...]]:
    # Must match generator: itertools.permutations(ALT,4) lex
    return list(itertools.permutations(alts, len(alts)))


def pos_map(perm: tuple[int, ...]) -> dict[int, int]:
    return {a: i for i, a in enumerate(perm)}


@dataclass(frozen=True)
class Schema:
    alts: list[int]
    pairs: list[tuple[int, int]]
    pair_idx: dict[tuple[int, int], int]
    nranks: int
    nprofiles: int
    npairs: int
    n_p_vars: int
    p_var_start: int
    p_var_end: int
    aux_start: int | None
    aux_end: int | None
    sel0_start: int | None
    sel0_end: int | None
    sel1_start: int | None
    sel1_end: int | None
    nvars: int

    def var_p(self, p: int, a: int, b: int) -> int:
        return 1 + p * self.npairs + self.pair_idx[(a, b)]

    def var_sel0(self, a: int, b: int) -> int:
        assert self.sel0_start is not None
        return self.sel0_start + self.pair_idx[(a, b)]

    def var_sel1(self, a: int, b: int) -> int:
        assert self.sel1_start is not None
        return self.sel1_start + self.pair_idx[(a, b)]


def build_schema(man: Manifest | None, *, cnf_nvars: int) -> Schema:
    alts = SPEC_ALT[:] if man is None else list(man.alts)
    pairs = SPEC_PAIRS[:] if man is None else list(man.pair_order)

    # Enforce the intended pair order spec (print discovered order if mismatch).
    if pairs != SPEC_PAIRS:
        print("ERROR: pair_order mismatch vs spec. Discovered order:", file=sys.stderr)
        print(pairs, file=sys.stderr)
        raise AuditError("pair_order does not match required spec order")

    if sorted(alts) != sorted(SPEC_ALT):
        raise AuditError(f"alts mismatch vs spec: {alts} (expected {SPEC_ALT})")
    if len(pairs) != 12 or len(set(pairs)) != 12:
        raise AuditError(f"pair_order must have 12 distinct pairs, got {pairs}")
    if any(a == b for (a, b) in pairs):
        raise AuditError("pair_order contains a==b")
    if set(pairs) != {(a, b) for a in alts for b in alts if a != b}:
        raise AuditError("pair_order is not exactly all ordered (a,b) with a!=b")

    pair_idx = {p: i for i, p in enumerate(pairs)}
    nranks = 24
    nprofiles = nranks * nranks
    npairs = len(pairs)
    n_p_vars = nprofiles * npairs
    p_var_start, p_var_end = 1, n_p_vars

    aux_start = aux_end = sel0_start = sel0_end = sel1_start = sel1_end = None
    if man is not None and man.aux_var_range is not None:
        aux_start, aux_end = man.aux_var_range
        if aux_start != n_p_vars + 1:
            raise AuditError(
                f"aux_var_range.start must be {n_p_vars+1}, got {aux_start}"
            )
        if aux_end != aux_start + 2 * npairs - 1:
            raise AuditError(
                f"aux_var_range.end must be {aux_start + 2*npairs - 1}, got {aux_end}"
            )
        sel0_start, sel0_end = aux_start, aux_start + npairs - 1
        sel1_start, sel1_end = aux_start + npairs, aux_end

    expected_nvars = n_p_vars if aux_start is None else aux_end
    if cnf_nvars != expected_nvars:
        raise AuditError(f"CNF nvars={cnf_nvars}, expected {expected_nvars}")

    return Schema(
        alts=alts,
        pairs=pairs,
        pair_idx=pair_idx,
        nranks=nranks,
        nprofiles=nprofiles,
        npairs=npairs,
        n_p_vars=n_p_vars,
        p_var_start=p_var_start,
        p_var_end=p_var_end,
        aux_start=aux_start,
        aux_end=aux_end,
        sel0_start=sel0_start,
        sel0_end=sel0_end,
        sel1_start=sel1_start,
        sel1_end=sel1_end,
        nvars=cnf_nvars,
    )


def expected_asymm(schema: Schema) -> Counter[tuple[int, ...]]:
    out: Counter[tuple[int, ...]] = Counter()
    for p in range(schema.nprofiles):
        for a, b in schema.pairs:
            cl = (-schema.var_p(p, a, b), -schema.var_p(p, b, a))
            out[tuple(sorted(cl))] += 1
    return out


def expected_un(schema: Schema) -> Counter[tuple[int, ...]]:
    rankings = all_rankings(schema.alts)
    if len(rankings) != schema.nranks:
        raise AuditError(f"expected {schema.nranks} rankings, got {len(rankings)}")
    pos = [pos_map(r) for r in rankings]
    profiles = [(i, j) for i in range(schema.nranks) for j in range(schema.nranks)]
    if len(profiles) != schema.nprofiles:
        raise AuditError("profile enumeration mismatch")

    out: Counter[tuple[int, ...]] = Counter()
    for p, (r0, r1) in enumerate(profiles):
        pos0 = pos[r0]
        pos1 = pos[r1]
        for a, b in schema.pairs:
            if pos0[a] < pos0[b] and pos1[a] < pos1[b]:
                out[(schema.var_p(p, a, b),)] += 1
    return out


def expected_minlib_selectors(schema: Schema) -> dict[str, Counter[tuple[int, ...]]]:
    if schema.sel0_start is None or schema.sel1_start is None:
        raise AuditError("manifest must declare aux_var_range for selector MINLIB encoding")

    rankings = all_rankings(schema.alts)
    pos = [pos_map(r) for r in rankings]
    profiles = [(i, j) for i in range(schema.nranks) for j in range(schema.nranks)]

    # OR clauses (length 12 each)
    or0 = tuple(sorted(schema.var_sel0(a, b) for (a, b) in schema.pairs))
    or1 = tuple(sorted(schema.var_sel1(a, b) for (a, b) in schema.pairs))

    c_or0: Counter[tuple[int, ...]] = Counter()
    c_or1: Counter[tuple[int, ...]] = Counter()
    c_or0[or0] += 1
    c_or1[or1] += 1

    c_impl0: Counter[tuple[int, ...]] = Counter()
    c_impl1: Counter[tuple[int, ...]] = Counter()

    for p, (r0, r1) in enumerate(profiles):
        pos0 = pos[r0]
        pos1 = pos[r1]
        for a, b in schema.pairs:
            lit0 = schema.var_p(p, a, b) if pos0[a] < pos0[b] else schema.var_p(p, b, a)
            c_impl0[tuple(sorted((-schema.var_sel0(a, b), lit0)))] += 1
            lit1 = schema.var_p(p, a, b) if pos1[a] < pos1[b] else schema.var_p(p, b, a)
            c_impl1[tuple(sorted((-schema.var_sel1(a, b), lit1)))] += 1

    return {
        "minlib_or0": c_or0,
        "minlib_or1": c_or1,
        "minlib_impl0": c_impl0,
        "minlib_impl1": c_impl1,
    }


def expected_no_cycle3(schema: Schema) -> Counter[tuple[int, ...]]:
    triples = [
        (a, b, c)
        for a in schema.alts
        for b in schema.alts
        for c in schema.alts
        if len({a, b, c}) == 3
    ]
    if len(triples) != 24:
        raise AuditError(f"expected 24 ordered triples, got {len(triples)}")
    out: Counter[tuple[int, ...]] = Counter()
    for p in range(schema.nprofiles):
        for a, b, c in triples:
            cl = (
                -schema.var_p(p, a, b),
                -schema.var_p(p, b, c),
                -schema.var_p(p, c, a),
            )
            out[tuple(sorted(cl))] += 1
    return out


def expected_no_cycle4(schema: Schema) -> Counter[tuple[int, ...]]:
    quads = list(itertools.permutations(schema.alts, len(schema.alts)))
    if len(quads) != 24:
        raise AuditError(f"expected 24 ordered quads, got {len(quads)}")
    out: Counter[tuple[int, ...]] = Counter()
    for p in range(schema.nprofiles):
        for a, b, c, d in quads:
            cl = (
                -schema.var_p(p, a, b),
                -schema.var_p(p, b, c),
                -schema.var_p(p, c, d),
                -schema.var_p(p, d, a),
            )
            out[tuple(sorted(cl))] += 1
    return out


def counter_sub(a: Counter[tuple[int, ...]], b: Counter[tuple[int, ...]]) -> Counter[tuple[int, ...]]:
    # multiset difference a - b, keeping only positive counts
    out: Counter[tuple[int, ...]] = Counter()
    for k, av in a.items():
        bv = b.get(k, 0)
        if av > bv:
            out[k] = av - bv
    return out


def fmt_clause(cl: tuple[int, ...]) -> str:
    return " ".join(str(x) for x in cl) + " 0"


def top_k(counter: Counter[tuple[int, ...]], k: int) -> list[tuple[tuple[int, ...], int]]:
    return sorted(counter.items(), key=lambda kv: (-kv[1], kv[0]))[:k]


def _fmt_counts(counts: dict[str, int], keys: list[str]) -> str:
    return "{" + ", ".join(f"{k}={counts.get(k, '∅')}" for k in keys) + "}"


def _validate_manifest(man: Manifest, schema: Schema, *, cnf_nvars: int, cnf_nclauses: int) -> None:
    # Basic field agreement with CNF header
    if man.nvars != cnf_nvars:
        raise AuditError(f"manifest.nvars={man.nvars} but CNF header nvars={cnf_nvars}")
    if man.nclauses != cnf_nclauses:
        raise AuditError(f"manifest.nclauses={man.nclauses} but CNF header nclauses={cnf_nclauses}")

    # Agreement with derived schema
    if man.nranks != schema.nranks:
        raise AuditError(f"manifest.nranks={man.nranks} expected {schema.nranks}")
    if man.nprofiles != schema.nprofiles:
        raise AuditError(f"manifest.nprofiles={man.nprofiles} expected {schema.nprofiles}")
    if man.npairs != schema.npairs:
        raise AuditError(f"manifest.npairs={man.npairs} expected {schema.npairs}")
    if man.n_p_vars != schema.n_p_vars:
        raise AuditError(f"manifest.n_p_vars={man.n_p_vars} expected {schema.n_p_vars}")
    if man.p_var_range != (schema.p_var_start, schema.p_var_end):
        raise AuditError(
            f"manifest.p_var_range={man.p_var_range} expected {(schema.p_var_start, schema.p_var_end)}"
        )
    expected_aux = None if schema.aux_start is None else (schema.aux_start, schema.aux_end)
    if man.aux_var_range != expected_aux:
        raise AuditError(f"manifest.aux_var_range={man.aux_var_range} expected {expected_aux}")

    # Internal manifest arithmetic sanity
    if man.nprofiles * man.npairs != man.n_p_vars:
        raise AuditError(
            f"manifest n_p_vars mismatch: nprofiles*npairs={man.nprofiles * man.npairs} but n_p_vars={man.n_p_vars}"
        )
    if man.category_counts is None:
        raise AuditError("manifest.category_counts missing")
    required = {"asymm", "un", "minlib", "no_cycle3", "no_cycle4"}
    missing = sorted(required - set(man.category_counts.keys()))
    if missing:
        raise AuditError(f"manifest.category_counts missing keys: {missing}")
    cat_sum = sum(int(v) for v in man.category_counts.values())
    if cat_sum != man.nclauses:
        raise AuditError(
            f"sum(manifest.category_counts.values())={cat_sum} but manifest.nclauses={man.nclauses}"
        )
    if cat_sum != cnf_nclauses:
        raise AuditError(
            f"sum(manifest.category_counts.values())={cat_sum} but CNF header nclauses={cnf_nclauses}"
        )


def audit(
    cnf_path: Path,
    manifest_path: Path | None,
    *,
    strict_duplicates: bool,
    fail_on_tautology: bool,
) -> None:
    man = None
    if manifest_path is not None:
        man = load_manifest(manifest_path, cnf_path)

    cnf_nvars, cnf_nclauses, raw_clauses = parse_dimacs(cnf_path)
    schema = build_schema(man, cnf_nvars=cnf_nvars)

    if man is not None:
        _validate_manifest(man, schema, cnf_nvars=cnf_nvars, cnf_nclauses=cnf_nclauses)

    # Canonicalize clauses; separate tautologies (allowed but warned).
    warn_cap = 20
    duplicate_count = 0
    duplicate_examples: list[str] = []
    tautology_count = 0
    tautology_examples: list[str] = []

    actual_all: Counter[tuple[int, ...]] = Counter()
    for lineno, lits in raw_clauses:
        cl, taut, had_dups = canon_clause(
            lits, path=cnf_path, lineno=lineno, strict_duplicates=strict_duplicates
        )
        if had_dups:
            duplicate_count += 1
            if len(duplicate_examples) < warn_cap:
                duplicate_examples.append(f"{cnf_path}:{lineno}: {lits} 0")
        if taut:
            tautology_count += 1
            if len(tautology_examples) < warn_cap:
                tautology_examples.append(f"{cnf_path}:{lineno}: {lits} 0")
            continue
        actual_all[cl] += 1

    if duplicate_count and not strict_duplicates:
        print(
            f"[warning] duplicate literals in {duplicate_count} clause(s); de-duplicated for comparison"
        )
        for ex in duplicate_examples:
            print(f"  {ex}")
        if duplicate_count > len(duplicate_examples):
            print(f"  ... ({duplicate_count - len(duplicate_examples)} more)")

    if tautology_count:
        prefix = "[error]" if fail_on_tautology else "[warning]"
        print(f"{prefix} tautological clauses: {tautology_count} (ignored for comparison)")
        for ex in tautology_examples:
            print(f"  {ex}")
        if tautology_count > len(tautology_examples):
            print(f"  ... ({tautology_count - len(tautology_examples)} more)")
        if fail_on_tautology:
            raise AuditError("tautological clause(s) present (use without --fail-on-tautology to ignore)")

    # Expected clauses (multisets)
    exp_asymm = expected_asymm(schema)
    exp_un = expected_un(schema)
    exp_c3 = expected_no_cycle3(schema)
    exp_c4 = expected_no_cycle4(schema)

    exp_minlib_parts: dict[str, Counter[tuple[int, ...]]] = {}
    if man is None:
        raise AuditError("manifest is required for MINLIB audit (aux vars + mode)")
    if man.minlib_mode != "selectors_v1":
        raise AuditError(f"unsupported MINLIB mode in manifest: {man.minlib_mode!r}")
    exp_minlib_parts = expected_minlib_selectors(schema)

    expected_by_cat: dict[str, Counter[tuple[int, ...]]] = {
        "asymm": exp_asymm,
        "un": exp_un,
        "no_cycle3": exp_c3,
        "no_cycle4": exp_c4,
        **exp_minlib_parts,
    }

    # Observed by structural category (for nicer error reports).
    obs_by_cat: dict[str, Counter[tuple[int, ...]]] = {k: Counter() for k in expected_by_cat}
    unexpected: Counter[tuple[int, ...]] = Counter()

    def in_range(v: int, lo: int, hi: int) -> bool:
        return lo <= v <= hi

    for cl, cnt in actual_all.items():
        lits = cl
        abs_vars = [abs(x) for x in lits]

        # UN
        if len(lits) == 1 and lits[0] > 0 and in_range(lits[0], schema.p_var_start, schema.p_var_end):
            obs_by_cat["un"][lits] += cnt
            continue

        # ASYMM
        if (
            len(lits) == 2
            and lits[0] < 0
            and lits[1] < 0
            and all(in_range(v, schema.p_var_start, schema.p_var_end) for v in abs_vars)
        ):
            obs_by_cat["asymm"][lits] += cnt
            continue

        # NO_CYCLE3
        if (
            len(lits) == 3
            and all(x < 0 for x in lits)
            and all(in_range(v, schema.p_var_start, schema.p_var_end) for v in abs_vars)
        ):
            obs_by_cat["no_cycle3"][lits] += cnt
            continue

        # NO_CYCLE4
        if (
            len(lits) == 4
            and all(x < 0 for x in lits)
            and all(in_range(v, schema.p_var_start, schema.p_var_end) for v in abs_vars)
        ):
            obs_by_cat["no_cycle4"][lits] += cnt
            continue

        # MINLIB parts
        if schema.sel0_start is not None and schema.sel0_end is not None:
            # OR0 / OR1 (length 12)
            if len(lits) == schema.npairs and all(x > 0 for x in lits):
                if all(in_range(v, schema.sel0_start, schema.sel0_end) for v in abs_vars):
                    obs_by_cat["minlib_or0"][lits] += cnt
                    continue
                if schema.sel1_start is not None and schema.sel1_end is not None and all(
                    in_range(v, schema.sel1_start, schema.sel1_end) for v in abs_vars
                ):
                    obs_by_cat["minlib_or1"][lits] += cnt
                    continue

            # IMPL0 / IMPL1 (binary)
            if len(lits) == 2:
                negs = [x for x in lits if x < 0]
                poss = [x for x in lits if x > 0]
                if len(negs) == 1 and len(poss) == 1:
                    negv = abs(negs[0])
                    posv = poss[0]
                    if in_range(posv, schema.p_var_start, schema.p_var_end):
                        if in_range(negv, schema.sel0_start, schema.sel0_end):
                            obs_by_cat["minlib_impl0"][lits] += cnt
                            continue
                        if schema.sel1_start is not None and schema.sel1_end is not None and in_range(
                            negv, schema.sel1_start, schema.sel1_end
                        ):
                            obs_by_cat["minlib_impl1"][lits] += cnt
                            continue

        unexpected[lits] += cnt

    def unclassified_reason(lits: tuple[int, ...]) -> str:
        allowed_lens = {1, 2, 3, 4, schema.npairs}
        if len(lits) not in allowed_lens:
            return f"length not in {sorted(allowed_lens)}"
        if schema.aux_start is not None and any(
            schema.aux_start <= abs(x) <= (schema.aux_end or schema.aux_start) for x in lits
        ):
            return "contains aux vars in unexpected places"
        has_pos = any(x > 0 for x in lits)
        has_neg = any(x < 0 for x in lits)
        if has_pos and has_neg:
            return "mixed signs not matching any category"
        return "shape not matching any category"

    unexpected_reasons: dict[tuple[int, ...], str] = {}
    for cl in unexpected:
        unexpected_reasons[cl] = unclassified_reason(cl)

    # Report / compare category-by-category.
    errors: list[str] = []

    def check_cat(name: str) -> None:
        exp = expected_by_cat[name]
        obs = obs_by_cat[name]
        exp_n = sum(exp.values())
        obs_n = sum(obs.values())
        print(f"[{name}] expected={exp_n} observed={obs_n}")
        missing = counter_sub(exp, obs)
        extra = counter_sub(obs, exp)
        if missing:
            errors.append(f"{name}: missing {sum(missing.values())} clauses")
            print(f"  missing (top 10):")
            for cl, n in top_k(missing, 10):
                print(f"    {n}×  {fmt_clause(cl)}")
        if extra:
            errors.append(f"{name}: unexpected {sum(extra.values())} clauses")
            print(f"  unexpected (top 10):")
            for cl, n in top_k(extra, 10):
                print(f"    {n}×  {fmt_clause(cl)}")

    for name in [
        "asymm",
        "un",
        "minlib_or0",
        "minlib_or1",
        "minlib_impl0",
        "minlib_impl1",
        "no_cycle3",
        "no_cycle4",
    ]:
        check_cat(name)

    if unexpected:
        errors.append(f"unclassified: {sum(unexpected.values())} clauses")
        len_hist: Counter[int] = Counter()
        for cl, n in unexpected.items():
            len_hist[len(cl)] += n
        print("[unclassified] unexpected clause shapes (top 10):")
        for cl, n in top_k(unexpected, 10):
            print(f"  {n}×  {fmt_clause(cl)}  # {unexpected_reasons.get(cl, '')}")
        print(
            "[unclassified] length histogram: "
            + ", ".join(f"{k}:{len_hist[k]}" for k in sorted(len_hist))
        )

    # Cross-check manifest counts (if present).
    if man is not None:
        expected_counts = {
            "asymm": sum(exp_asymm.values()),
            "un": sum(exp_un.values()),
            "minlib": sum(sum(c.values()) for c in exp_minlib_parts.values()),
            "no_cycle3": sum(exp_c3.values()),
            "no_cycle4": sum(exp_c4.values()),
        }
        for k, exp_n in expected_counts.items():
            if man.category_counts[k] != exp_n:
                errors.append(
                    f"manifest.category_counts[{k}]={man.category_counts[k]} expected {exp_n}"
                )

    if errors:
        print("\nFAILED:")
        for e in errors:
            print(f"- {e}")
        if man is not None:
            keys = ["asymm", "un", "minlib", "no_cycle3", "no_cycle4"]
            print(
                "[summary] "
                f"manifest nvars={man.nvars} nclauses={man.nclauses} counts={_fmt_counts(man.category_counts, keys)}; "
                f"expected counts={_fmt_counts(expected_counts, keys)}"
            )
        raise AuditError("CNF audit failed")

    print("\nOK: CNF matches spec and manifest.")
    if man is not None:
        keys = ["asymm", "un", "minlib", "no_cycle3", "no_cycle4"]
        print(
            "[summary] "
            f"manifest nvars={man.nvars} nclauses={man.nclauses} counts={_fmt_counts(man.category_counts, keys)}; "
            f"expected counts={_fmt_counts(expected_counts, keys)}"
        )


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("cnf", type=Path, help="DIMACS CNF file (e.g. Certificates/sen24.cnf)")
    ap.add_argument("--manifest", type=Path, default=None, help="JSON manifest path")
    ap.add_argument(
        "--strict-duplicates",
        action="store_true",
        help="Fail if any clause contains duplicate literals (default: warn + de-duplicate)",
    )
    ap.add_argument(
        "--fail-on-tautology",
        action="store_true",
        help="Fail if any tautological clause is present (default: warn + ignore)",
    )
    args = ap.parse_args()
    audit(
        args.cnf,
        args.manifest,
        strict_duplicates=args.strict_duplicates,
        fail_on_tautology=args.fail_on_tautology,
    )


if __name__ == "__main__":
    try:
        main()
    except AuditError as e:
        print(f"ERROR: {e}", file=sys.stderr)
        sys.exit(1)
