#!/usr/bin/env python3
"""
Mechanical auditor for the parametric finite-schema CNF family.

This checker validates:
  - manifest/schema agreement,
  - variable family ranges,
  - pair/triple/quad/profile enumeration discipline,
  - clause-shape validity for enabled lever families,
  - expected category counts for tested finite instances.

It intentionally leaves `scripts/check_sen24_cnf.py` in place as the exact baseline
auditor for the committed Sen24 proof artifact.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import sys
from dataclasses import dataclass
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from encoding.schema import (  # noqa: E402
    LEGACY_MINLIB_MODE,
    PARAMETRIC_MINLIB_MODE,
    FiniteSchema,
)


CATEGORY_KEYS = ["asymm", "un", "minlib", "no_cycle3", "no_cycle4"]
AXIOM_KEYS = set(CATEGORY_KEYS)


class AuditError(RuntimeError):
    pass


def sha256_file(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as f:
        for chunk in iter(lambda: f.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def parse_dimacs_header(path: Path) -> tuple[int, int]:
    nvars = None
    nclauses = None
    with path.open("r", encoding="utf-8") as f:
        for lineno, raw in enumerate(f, start=1):
            line = raw.strip()
            if not line or line.startswith("c"):
                continue
            if not line.startswith("p "):
                raise AuditError(f"{path}:{lineno}: clause before header")
            parts = line.split()
            if parts[:2] != ["p", "cnf"] or len(parts) != 4:
                raise AuditError(f"{path}:{lineno}: malformed header: {raw.rstrip()!r}")
            nvars = int(parts[2])
            nclauses = int(parts[3])
            break
    if nvars is None or nclauses is None:
        raise AuditError(f"{path}: missing 'p cnf' header")
    return nvars, nclauses


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


@dataclass(frozen=True)
class ManifestInfo:
    encoding: str
    n_voters: int
    n_alts: int
    voters: list[int]
    alts: list[int]
    pair_order: list[tuple[int, int]]
    axioms: list[str]
    nranks: int
    nprofiles: int
    npairs: int
    ntriples: int | None
    nquads: int | None
    n_p_vars: int
    nvars: int
    nclauses: int
    category_counts: dict[str, int]
    minlib_mode: str
    p_var_range: tuple[int, int]
    aux_var_range: tuple[int, int] | None
    cnf_sha256: str
    ranking_order: str | None
    profile_order: str | None
    triple_order: str | None
    quad_order: str | None


def load_manifest(path: Path, cnf_path: Path) -> ManifestInfo:
    obj = json.loads(path.read_text(encoding="utf-8"))
    encoding = str(obj.get("encoding"))
    if encoding == "sen24":
        n_voters = 2
        n_alts = 4
        voters = [0, 1]
        ntriples = None
        nquads = None
    elif encoding == "finite_schema_v1":
        n_voters = int(obj["n_voters"])
        n_alts = int(obj["n_alts"])
        voters = [int(v) for v in obj["voters"]]
        ntriples = int(obj["ntriples"])
        nquads = int(obj["nquads"])
    else:
        raise AuditError(
            f"manifest.encoding must be 'sen24' or 'finite_schema_v1', got {encoding!r}"
        )

    cnf_sha = sha256_file(cnf_path)
    if "cnf_sha256" in obj and obj["cnf_sha256"] != cnf_sha:
        raise AuditError(
            "manifest.cnf_sha256 does not match CNF file: "
            f"{obj['cnf_sha256']} (manifest) vs {cnf_sha} (file)"
        )

    aux_range = None
    if obj.get("aux_var_range") is not None:
        aux_range = (int(obj["aux_var_range"][0]), int(obj["aux_var_range"][1]))

    return ManifestInfo(
        encoding=encoding,
        n_voters=n_voters,
        n_alts=n_alts,
        voters=voters,
        alts=[int(a) for a in obj["alts"]],
        pair_order=[tuple(int(x) for x in pair) for pair in obj["pair_order"]],
        axioms=[str(x) for x in obj.get("axioms", [])],
        nranks=int(obj["nranks"]),
        nprofiles=int(obj["nprofiles"]),
        npairs=int(obj["npairs"]),
        ntriples=ntriples,
        nquads=nquads,
        n_p_vars=int(obj["n_p_vars"]),
        nvars=int(obj["nvars"]),
        nclauses=int(obj["nclauses"]),
        category_counts={k: int(v) for k, v in obj["category_counts"].items()},
        minlib_mode=str(obj.get("minlib", {}).get("mode", "disabled")),
        p_var_range=(int(obj["p_var_range"][0]), int(obj["p_var_range"][1])),
        aux_var_range=aux_range,
        cnf_sha256=cnf_sha,
        ranking_order=obj.get("ranking_order"),
        profile_order=obj.get("profile_order"),
        triple_order=obj.get("triple_order"),
        quad_order=obj.get("quad_order"),
    )


def expected_full_category_counts(schema: FiniteSchema) -> dict[str, int]:
    un_count = 0
    for p in range(schema.n_profiles):
        for a, b in schema.pairs:
            if schema.all_voters_prefer(p, a, b):
                un_count += 1

    if schema.minlib_mode == "disabled":
        minlib_count = 0
    elif schema.minlib_mode == LEGACY_MINLIB_MODE:
        minlib_count = 2 + 2 * schema.n_profiles * schema.n_pairs
    elif schema.minlib_mode == PARAMETRIC_MINLIB_MODE:
        minlib_count = (
            1
            + 2 * len(schema.minlib_voter_pairs)
            + schema.n_voters * schema.n_pairs * schema.n_profiles
        )
    else:
        raise AuditError(f"unsupported MINLIB mode {schema.minlib_mode!r}")

    return {
        "asymm": schema.n_profiles * schema.n_pairs,
        "un": un_count,
        "minlib": minlib_count,
        "no_cycle3": schema.n_profiles * len(schema.triples),
        "no_cycle4": schema.n_profiles * len(schema.quads),
    }


def _fmt_counts(counts: dict[str, int], keys: list[str]) -> str:
    return "{" + ", ".join(f"{k}={counts.get(k, '∅')}" for k in keys) + "}"


def normalize_cycle(edges: list[tuple[int, int]]) -> tuple[int, ...] | None:
    out_map: dict[int, int] = {}
    in_map: dict[int, int] = {}
    for src, dst in edges:
        if src == dst or src in out_map or dst in in_map:
            return None
        out_map[src] = dst
        in_map[dst] = src
    verts = sorted(set(out_map) | set(in_map))
    if len(verts) != len(edges):
        return None
    start = min(verts)
    cycle = [start]
    cur = start
    for _ in range(len(edges) - 1):
        nxt = out_map.get(cur)
        if nxt is None or nxt == start:
            return None
        cycle.append(nxt)
        cur = nxt
    if out_map.get(cur) != start:
        return None
    return tuple(cycle)


def decode_p_var(schema: FiniteSchema, var: int) -> tuple[int, int, int, int]:
    idx = var - 1
    p = idx // schema.n_pairs
    pair_idx = idx % schema.n_pairs
    a, b = schema.pairs[pair_idx]
    return p, pair_idx, a, b


def build_cycle_rep_index(schema: FiniteSchema, length: int) -> dict[tuple[int, ...], int]:
    reps: dict[tuple[int, ...], int] = {}
    tuples = schema.triples if length == 3 else schema.quads
    for tup in tuples:
        edges = list(zip(tup, tup[1:] + tup[:1]))
        rep = normalize_cycle(edges)
        if rep is None:
            raise AuditError(f"failed to normalize expected {length}-cycle tuple {tup}")
        if rep not in reps:
            reps[rep] = len(reps)
    return reps


def audit(
    cnf_path: Path,
    manifest_path: Path,
    *,
    strict_duplicates: bool,
    fail_on_tautology: bool,
) -> None:
    man = load_manifest(manifest_path, cnf_path)
    schema = FiniteSchema(
        n=man.n_voters,
        m=man.n_alts,
        minlib_mode=man.minlib_mode,
    )

    header_nvars, header_nclauses = parse_dimacs_header(cnf_path)
    if header_nvars != man.nvars:
        raise AuditError(f"CNF nvars={header_nvars} but manifest.nvars={man.nvars}")
    if header_nclauses != man.nclauses:
        raise AuditError(f"CNF nclauses={header_nclauses} but manifest.nclauses={man.nclauses}")

    if man.alts != schema.alts:
        raise AuditError(f"manifest alts={man.alts} expected {schema.alts}")
    if man.voters != schema.voters:
        raise AuditError(f"manifest voters={man.voters} expected {schema.voters}")
    if man.pair_order != schema.pairs:
        raise AuditError("manifest pair_order does not match schema pair enumeration")
    if man.nranks != schema.n_ranks:
        raise AuditError(f"manifest.nranks={man.nranks} expected {schema.n_ranks}")
    if man.nprofiles != schema.n_profiles:
        raise AuditError(f"manifest.nprofiles={man.nprofiles} expected {schema.n_profiles}")
    if man.npairs != schema.n_pairs:
        raise AuditError(f"manifest.npairs={man.npairs} expected {schema.n_pairs}")
    if man.n_p_vars != schema.n_p_vars:
        raise AuditError(f"manifest.n_p_vars={man.n_p_vars} expected {schema.n_p_vars}")
    if man.nvars != schema.n_vars:
        raise AuditError(f"manifest.nvars={man.nvars} expected {schema.n_vars}")
    if man.p_var_range != (1, schema.n_p_vars):
        raise AuditError(f"manifest.p_var_range={man.p_var_range} expected {(1, schema.n_p_vars)}")
    expected_aux = None if schema.aux_var_range is None else schema.aux_var_range
    if man.aux_var_range != expected_aux:
        raise AuditError(
            f"manifest.aux_var_range={man.aux_var_range} expected {expected_aux}"
        )
    if man.ntriples is not None and man.ntriples != schema.n_triples:
        raise AuditError(f"manifest.ntriples={man.ntriples} expected {schema.n_triples}")
    if man.nquads is not None and man.nquads != schema.n_quads:
        raise AuditError(f"manifest.nquads={man.nquads} expected {schema.n_quads}")
    if man.ranking_order is not None and man.ranking_order != schema.ranking_order:
        raise AuditError(
            f"manifest.ranking_order={man.ranking_order!r} expected {schema.ranking_order!r}"
        )
    expected_profile_order = (
        "p = r0*24 + r1 (r0 major)"
        if man.encoding == "sen24"
        else schema.profile_order
    )
    if man.profile_order is not None and man.profile_order != expected_profile_order:
        raise AuditError(
            f"manifest.profile_order={man.profile_order!r} expected {expected_profile_order!r}"
        )
    if man.triple_order is not None and man.triple_order != schema.triple_order:
        raise AuditError(
            f"manifest.triple_order={man.triple_order!r} expected {schema.triple_order!r}"
        )
    if man.quad_order is not None and man.quad_order != schema.quad_order:
        raise AuditError(
            f"manifest.quad_order={man.quad_order!r} expected {schema.quad_order!r}"
        )

    missing_keys = sorted(set(CATEGORY_KEYS) - set(man.category_counts))
    if missing_keys:
        raise AuditError(f"manifest.category_counts missing keys: {missing_keys}")
    unknown_count_keys = sorted(set(man.category_counts) - set(CATEGORY_KEYS))
    if unknown_count_keys:
        raise AuditError(f"manifest.category_counts unknown keys: {unknown_count_keys}")

    full_counts = expected_full_category_counts(schema)
    cat_sum = sum(man.category_counts.values())
    if cat_sum != man.nclauses:
        raise AuditError(
            f"sum(manifest.category_counts.values())={cat_sum} but manifest.nclauses={man.nclauses}"
        )
    for key in CATEGORY_KEYS:
        count = man.category_counts[key]
        full = full_counts[key]
        if count not in {0, full}:
            raise AuditError(
                f"manifest.category_counts[{key}]={count} must be 0 or full={full}"
            )

    if man.axioms:
        unknown_axioms = sorted(set(man.axioms) - AXIOM_KEYS)
        if unknown_axioms:
            raise AuditError(f"manifest.axioms contains unknown entries: {unknown_axioms}")
        for key in CATEGORY_KEYS:
            enabled = key in man.axioms
            expected = full_counts[key] if enabled else 0
            if man.category_counts[key] != expected:
                raise AuditError(
                    f"manifest mismatch for {key}: axioms says {'on' if enabled else 'off'} "
                    f"but category_counts[{key}]={man.category_counts[key]} expected {expected}"
                )

    unordered_pairs = [(a, b) for a in schema.alts for b in schema.alts if a < b]
    unordered_pair_idx = {pair: idx for idx, pair in enumerate(unordered_pairs)}
    cycle3_idx = build_cycle_rep_index(schema, 3) if schema.triples else {}
    cycle4_idx = build_cycle_rep_index(schema, 4) if schema.quads else {}

    actual_un = bytearray(schema.n_p_vars + 1)
    actual_asymm = bytearray(schema.n_profiles * len(unordered_pairs))
    actual_cycle3 = bytearray(schema.n_profiles * max(1, len(cycle3_idx)))
    actual_cycle4 = bytearray(schema.n_profiles * max(1, len(cycle4_idx)))

    actual_minlib_or0 = 0
    actual_minlib_or1 = 0
    actual_minlib_impl0 = bytearray(schema.n_profiles * schema.n_pairs)
    actual_minlib_impl1 = bytearray(schema.n_profiles * schema.n_pairs)

    actual_minlib_pair_or = 0
    actual_minlib_pair_support_left = bytearray(max(1, len(schema.minlib_voter_pairs)))
    actual_minlib_pair_support_right = bytearray(max(1, len(schema.minlib_voter_pairs)))
    actual_minlib_decisive = bytearray(max(1, schema.n_voters * schema.n_pairs * schema.n_profiles))

    warn_cap = 20
    duplicate_count = 0
    duplicate_examples: list[str] = []
    tautology_count = 0
    tautology_examples: list[str] = []
    errors: list[str] = []
    unclassified_examples: list[str] = []
    unclassified_count = 0
    seen_clause_count = 0

    def note_unclassified(path: Path, lineno: int, clause: tuple[int, ...], reason: str) -> None:
        nonlocal unclassified_count
        unclassified_count += 1
        if len(unclassified_examples) < 10:
            clause_text = " ".join(str(x) for x in clause) + " 0"
            unclassified_examples.append(f"{path}:{lineno}: {clause_text} # {reason}")

    def bump(buf: bytearray, idx: int, *, desc: str, path: Path, lineno: int) -> None:
        if idx < 0 or idx >= len(buf):
            raise AuditError(f"{path}:{lineno}: internal auditor index out of range for {desc}")
        if buf[idx] == 255:
            raise AuditError(f"{path}:{lineno}: {desc} overflow")
        buf[idx] += 1

    with cnf_path.open("r", encoding="utf-8") as f:
        header_seen = False
        for lineno, raw in enumerate(f, start=1):
            line = raw.strip()
            if not line or line.startswith("c"):
                continue
            if not header_seen:
                if not line.startswith("p "):
                    raise AuditError(f"{cnf_path}:{lineno}: clause before header")
                header_seen = True
                continue

            try:
                ints = [int(x) for x in line.split()]
            except ValueError as e:
                raise AuditError(f"{cnf_path}:{lineno}: non-integer literal") from e
            if not ints or ints[-1] != 0:
                raise AuditError(f"{cnf_path}:{lineno}: clause does not end with 0")
            if 0 in ints[:-1]:
                raise AuditError(f"{cnf_path}:{lineno}: clause contains 0 before terminator")

            lits_raw = ints[:-1]
            for lit in lits_raw:
                if abs(lit) > header_nvars:
                    raise AuditError(
                        f"{cnf_path}:{lineno}: literal {lit} out of range for nvars={header_nvars}"
                    )

            clause, taut, had_dups = canon_clause(
                lits_raw, path=cnf_path, lineno=lineno, strict_duplicates=strict_duplicates
            )
            seen_clause_count += 1

            if had_dups:
                duplicate_count += 1
                if len(duplicate_examples) < warn_cap:
                    duplicate_examples.append(f"{cnf_path}:{lineno}: {lits_raw} 0")
            if taut:
                tautology_count += 1
                if len(tautology_examples) < warn_cap:
                    tautology_examples.append(f"{cnf_path}:{lineno}: {lits_raw} 0")
                continue

            abs_vars = [abs(x) for x in clause]
            if any(v < 1 or v > schema.n_vars for v in abs_vars):
                raise AuditError(f"{cnf_path}:{lineno}: literal outside schema variable range")

            classified = False

            if len(clause) == 1 and clause[0] > 0:
                var = clause[0]
                if 1 <= var <= schema.n_p_vars:
                    p, _, a, b = decode_p_var(schema, var)
                    if schema.all_voters_prefer(p, a, b):
                        bump(actual_un, var, desc="un", path=cnf_path, lineno=lineno)
                        classified = True
                elif (
                    schema.minlib_mode == PARAMETRIC_MINLIB_MODE
                    and schema.minlib_pair_selector_start is not None
                    and schema.minlib_pair_selector_start
                    <= var
                    <= (schema.minlib_pair_selector_end or schema.minlib_pair_selector_start)
                    and len(schema.minlib_voter_pairs) == 1
                ):
                    actual_minlib_pair_or += 1
                    classified = True

            if not classified and len(clause) == 2:
                negs = [x for x in clause if x < 0]
                poss = [x for x in clause if x > 0]
                if len(negs) == 2 and len(poss) == 0:
                    if not all(1 <= abs(lit) <= schema.n_p_vars for lit in clause):
                        note_unclassified(
                            cnf_path,
                            lineno,
                            clause,
                            "binary negative clause uses non-social variable",
                        )
                        continue
                    p0, _, a0, b0 = decode_p_var(schema, abs(negs[0]))
                    p1, _, a1, b1 = decode_p_var(schema, abs(negs[1]))
                    if p0 == p1 and (a1, b1) == (b0, a0):
                        up = tuple(sorted((a0, b0)))
                        idx = p0 * len(unordered_pairs) + unordered_pair_idx[up]
                        bump(actual_asymm, idx, desc="asymm", path=cnf_path, lineno=lineno)
                        classified = True
                elif len(negs) == 1 and len(poss) == 1:
                    negv = abs(negs[0])
                    posv = poss[0]
                    if schema.minlib_mode == LEGACY_MINLIB_MODE and 1 <= posv <= schema.n_p_vars:
                        p, _, _, _ = decode_p_var(schema, posv)
                        if schema.sel0_start is not None and schema.sel0_start <= negv <= schema.sel0_end:
                            pair_idx = negv - schema.sel0_start
                            a, b = schema.pairs[pair_idx]
                            expected = (
                                schema.var_p(p, a, b)
                                if schema.pref0(p, a, b)
                                else schema.var_p(p, b, a)
                            )
                            if posv == expected:
                                idx = p * schema.n_pairs + pair_idx
                                bump(
                                    actual_minlib_impl0,
                                    idx,
                                    desc="minlib_impl0",
                                    path=cnf_path,
                                    lineno=lineno,
                                )
                                classified = True
                        if (
                            not classified
                            and schema.sel1_start is not None
                            and schema.sel1_start <= negv <= schema.sel1_end
                        ):
                            pair_idx = negv - schema.sel1_start
                            a, b = schema.pairs[pair_idx]
                            expected = (
                                schema.var_p(p, a, b)
                                if schema.pref1(p, a, b)
                                else schema.var_p(p, b, a)
                            )
                            if posv == expected:
                                idx = p * schema.n_pairs + pair_idx
                                bump(
                                    actual_minlib_impl1,
                                    idx,
                                    desc="minlib_impl1",
                                    path=cnf_path,
                                    lineno=lineno,
                                )
                                classified = True
                    elif (
                        schema.minlib_mode == PARAMETRIC_MINLIB_MODE
                        and 1 <= posv <= schema.n_p_vars
                        and schema.minlib_decisive_selector_start is not None
                        and schema.minlib_decisive_selector_start <= negv <= schema.minlib_decisive_selector_end
                    ):
                        dec_idx = negv - schema.minlib_decisive_selector_start
                        voter = dec_idx // schema.n_pairs
                        pair_idx = dec_idx % schema.n_pairs
                        a, b = schema.pairs[pair_idx]
                        p, _, _, _ = decode_p_var(schema, posv)
                        expected = (
                            schema.var_p(p, a, b)
                            if schema.prefers(p, voter, a, b)
                            else schema.var_p(p, b, a)
                        )
                        if posv == expected:
                            idx = (
                                (voter * schema.n_pairs + pair_idx) * schema.n_profiles + p
                            )
                            bump(
                                actual_minlib_decisive,
                                idx,
                                desc="minlib_decisive",
                                path=cnf_path,
                                lineno=lineno,
                            )
                            classified = True

            if not classified and len(clause) == 3 and all(lit < 0 for lit in clause):
                if not all(1 <= abs(lit) <= schema.n_p_vars for lit in clause):
                    note_unclassified(
                        cnf_path,
                        lineno,
                        clause,
                        "3-literal negative clause uses non-social variable",
                    )
                    continue
                decoded = [decode_p_var(schema, abs(lit)) for lit in clause]
                profiles = {item[0] for item in decoded}
                if len(profiles) == 1:
                    edges = [(a, b) for (_, _, a, b) in decoded]
                    rep = normalize_cycle(edges)
                    if rep is not None and rep in cycle3_idx:
                        p = decoded[0][0]
                        idx = p * len(cycle3_idx) + cycle3_idx[rep]
                        bump(actual_cycle3, idx, desc="no_cycle3", path=cnf_path, lineno=lineno)
                        classified = True

            if not classified and len(clause) == 4 and all(lit < 0 for lit in clause):
                if not all(1 <= abs(lit) <= schema.n_p_vars for lit in clause):
                    note_unclassified(
                        cnf_path,
                        lineno,
                        clause,
                        "4-literal negative clause uses non-social variable",
                    )
                    continue
                decoded = [decode_p_var(schema, abs(lit)) for lit in clause]
                profiles = {item[0] for item in decoded}
                if len(profiles) == 1:
                    edges = [(a, b) for (_, _, a, b) in decoded]
                    rep = normalize_cycle(edges)
                    if rep is not None and rep in cycle4_idx:
                        p = decoded[0][0]
                        idx = p * len(cycle4_idx) + cycle4_idx[rep]
                        bump(actual_cycle4, idx, desc="no_cycle4", path=cnf_path, lineno=lineno)
                        classified = True

            if not classified and schema.minlib_mode == LEGACY_MINLIB_MODE:
                if len(clause) == schema.n_pairs and all(lit > 0 for lit in clause):
                    clause_vars = list(clause)
                    if clause_vars == [schema.var_sel0(a, b) for (a, b) in schema.pairs]:
                        actual_minlib_or0 += 1
                        classified = True
                    elif clause_vars == [schema.var_sel1(a, b) for (a, b) in schema.pairs]:
                        actual_minlib_or1 += 1
                        classified = True

            if not classified and schema.minlib_mode == PARAMETRIC_MINLIB_MODE:
                if len(clause) == len(schema.minlib_voter_pairs) and all(lit > 0 for lit in clause):
                    expected_vars = [
                        schema.var_minlib_pair(i, j) for (i, j) in schema.minlib_voter_pairs
                    ]
                    if list(clause) == expected_vars:
                        actual_minlib_pair_or += 1
                        classified = True
                elif (
                    len(clause) == schema.minlib_support_clause_length()
                    and clause[0] < 0
                    and all(lit > 0 for lit in clause[1:])
                ):
                    negv = abs(clause[0])
                    if (
                        schema.minlib_pair_selector_start is not None
                        and schema.minlib_pair_selector_start
                        <= negv
                        <= (schema.minlib_pair_selector_end or schema.minlib_pair_selector_start)
                    ):
                        pair_idx = negv - schema.minlib_pair_selector_start
                        i, j = schema.minlib_voter_pairs[pair_idx]
                        left = [schema.var_minlib_decisive(i, a, b) for (a, b) in schema.pairs]
                        right = [schema.var_minlib_decisive(j, a, b) for (a, b) in schema.pairs]
                        if list(clause[1:]) == left:
                            bump(
                                actual_minlib_pair_support_left,
                                pair_idx,
                                desc="minlib_pair_support_left",
                                path=cnf_path,
                                lineno=lineno,
                            )
                            classified = True
                        elif list(clause[1:]) == right:
                            bump(
                                actual_minlib_pair_support_right,
                                pair_idx,
                                desc="minlib_pair_support_right",
                                path=cnf_path,
                                lineno=lineno,
                            )
                            classified = True

            if not classified:
                note_unclassified(cnf_path, lineno, clause, "shape does not match any enabled family")

    if seen_clause_count != header_nclauses:
        raise AuditError(
            f"{cnf_path}: header says {header_nclauses} clauses but parsed {seen_clause_count}"
        )

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
            raise AuditError("tautological clause(s) present")

    expected_un = bytearray(schema.n_p_vars + 1)
    if man.category_counts["un"]:
        for p in range(schema.n_profiles):
            for a, b in schema.pairs:
                if schema.all_voters_prefer(p, a, b):
                    expected_un[schema.var_p(p, a, b)] = 1

    expected_asymm_value = 2 if man.category_counts["asymm"] else 0
    expected_cycle3_value = 3 if man.category_counts["no_cycle3"] else 0
    expected_cycle4_value = 4 if man.category_counts["no_cycle4"] else 0

    def compare_bytearray(name: str, actual: bytearray, expected_value: int) -> tuple[int, int]:
        missing = 0
        extra = 0
        for value in actual:
            if value < expected_value:
                missing += expected_value - value
            elif value > expected_value:
                extra += value - expected_value
        observed = sum(actual)
        expected = expected_value * len(actual)
        print(f"[{name}] expected={expected} observed={observed}")
        if missing:
            errors.append(f"{name}: missing {missing} clause instance(s)")
        if extra:
            errors.append(f"{name}: unexpected {extra} clause instance(s)")
        return expected, observed

    expected_counts = {
        "asymm": man.category_counts["asymm"],
        "un": man.category_counts["un"],
        "minlib": man.category_counts["minlib"],
        "no_cycle3": man.category_counts["no_cycle3"],
        "no_cycle4": man.category_counts["no_cycle4"],
    }

    compare_bytearray("asymm", actual_asymm, expected_asymm_value)

    un_missing = 0
    un_extra = 0
    un_observed = 0
    un_expected = 0
    for var in range(1, schema.n_p_vars + 1):
        exp = expected_un[var]
        act = actual_un[var]
        un_expected += exp
        un_observed += act
        if act < exp:
            un_missing += exp - act
        elif act > exp:
            un_extra += act - exp
    print(f"[un] expected={un_expected} observed={un_observed}")
    if un_missing:
        errors.append(f"un: missing {un_missing} clause instance(s)")
    if un_extra:
        errors.append(f"un: unexpected {un_extra} clause instance(s)")

    compare_bytearray("no_cycle3", actual_cycle3[: schema.n_profiles * len(cycle3_idx)], expected_cycle3_value)
    compare_bytearray("no_cycle4", actual_cycle4[: schema.n_profiles * len(cycle4_idx)], expected_cycle4_value)

    minlib_observed = 0
    minlib_expected = man.category_counts["minlib"]
    if schema.minlib_mode == LEGACY_MINLIB_MODE:
        exp_or = 1 if man.category_counts["minlib"] else 0
        print(f"[minlib_or0] expected={exp_or} observed={actual_minlib_or0}")
        print(f"[minlib_or1] expected={exp_or} observed={actual_minlib_or1}")
        if actual_minlib_or0 != exp_or:
            errors.append(
                f"minlib_or0: expected {exp_or} occurrence(s), observed {actual_minlib_or0}"
            )
        if actual_minlib_or1 != exp_or:
            errors.append(
                f"minlib_or1: expected {exp_or} occurrence(s), observed {actual_minlib_or1}"
            )
        compare_bytearray(
            "minlib_impl0",
            actual_minlib_impl0,
            1 if man.category_counts["minlib"] else 0,
        )
        compare_bytearray(
            "minlib_impl1",
            actual_minlib_impl1,
            1 if man.category_counts["minlib"] else 0,
        )
        minlib_observed = actual_minlib_or0 + actual_minlib_or1 + sum(actual_minlib_impl0) + sum(actual_minlib_impl1)
    elif schema.minlib_mode == PARAMETRIC_MINLIB_MODE:
        exp_pair_or = 1 if man.category_counts["minlib"] else 0
        exp_support = 1 if man.category_counts["minlib"] else 0
        print(f"[minlib_pair_or] expected={exp_pair_or} observed={actual_minlib_pair_or}")
        if actual_minlib_pair_or != exp_pair_or:
            errors.append(
                f"minlib_pair_or: expected {exp_pair_or} occurrence(s), observed {actual_minlib_pair_or}"
            )
        compare_bytearray(
            "minlib_pair_support_left",
            actual_minlib_pair_support_left[: len(schema.minlib_voter_pairs)],
            exp_support,
        )
        compare_bytearray(
            "minlib_pair_support_right",
            actual_minlib_pair_support_right[: len(schema.minlib_voter_pairs)],
            exp_support,
        )
        compare_bytearray(
            "minlib_decisive",
            actual_minlib_decisive[: schema.n_voters * schema.n_pairs * schema.n_profiles],
            1 if man.category_counts["minlib"] else 0,
        )
        minlib_observed = (
            actual_minlib_pair_or
            + sum(actual_minlib_pair_support_left[: len(schema.minlib_voter_pairs)])
            + sum(actual_minlib_pair_support_right[: len(schema.minlib_voter_pairs)])
            + sum(actual_minlib_decisive[: schema.n_voters * schema.n_pairs * schema.n_profiles])
        )
    else:
        if man.category_counts["minlib"]:
            errors.append(f"unsupported minlib mode {schema.minlib_mode!r} with nonzero clause count")
        print("[minlib] expected=0 observed=0")
        minlib_observed = 0

    if minlib_observed != minlib_expected:
        errors.append(
            f"minlib aggregate count mismatch: expected {minlib_expected}, observed {minlib_observed}"
        )

    if unclassified_count:
        errors.append(f"unclassified: {unclassified_count} clause(s)")
        print("[unclassified] examples:")
        for ex in unclassified_examples:
            print(f"  {ex}")

    if errors:
        print("\nFAILED:")
        for err in errors:
            print(f"- {err}")
        print(
            "[summary] "
            f"manifest nvars={man.nvars} nclauses={man.nclauses} counts={_fmt_counts(man.category_counts, CATEGORY_KEYS)}; "
            f"full counts={_fmt_counts(full_counts, CATEGORY_KEYS)}"
        )
        raise AuditError("CNF audit failed")

    print("\nOK: CNF matches schema and manifest.")
    print(
        "[summary] "
        f"manifest nvars={man.nvars} nclauses={man.nclauses} counts={_fmt_counts(man.category_counts, CATEGORY_KEYS)}; "
        f"full counts={_fmt_counts(full_counts, CATEGORY_KEYS)}"
    )


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("cnf", type=Path, help="DIMACS CNF file")
    ap.add_argument("--manifest", type=Path, required=True, help="JSON manifest path")
    ap.add_argument(
        "--strict-duplicates",
        action="store_true",
        help="Fail if any clause contains duplicate literals",
    )
    ap.add_argument(
        "--fail-on-tautology",
        action="store_true",
        help="Fail if any tautological clause is present",
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
