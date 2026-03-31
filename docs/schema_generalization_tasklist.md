# Schema Generalization Tasklist
## Step 0 implementation record

**Status:** Code complete for the tested cases `(2,4)`, `(2,5)`, and `(3,4)`.  
**Remaining gate:** `docs/axiom_semantics_scaling.md` is still not signed off because the effective-strength and claim-scope judgment for `no_cycle3` and `no_cycle4` remains separate from Step 0.

---

## Implemented changes

- `encoding/schema.py`
  - Added `FiniteSchema(n, m, minlib_mode=...)`.
  - Added parametric helpers for voters, alternatives, profiles, ordered pairs, ordered triples, ordered quads, and voter/profile preference lookup.
  - Preserved `Sen24Schema(...)` as a compatibility wrapper for the audited Sen24 artifact path.
- `encoding/axioms/un.py`
  - Replaced the fixed two-voter helper with `schema.all_voters_prefer(...)`.
  - `un` is now encoded as profile-local unanimity / weak Pareto over all voters in the schema.
- `encoding/axioms/minlib.py`
  - Added a dispatcher over two explicit modes.
  - `selectors_v1` remains available only for `(2,4)` artifact compatibility.
  - `pair_selectors_v1` is the parametric mode used for neighboring cases.
- `encoding/axioms/minlib_pair_selectors_v1.py`
  - Added one selector for each unordered pair of distinct voters.
  - Added one decisive-witness variable for each `(voter, ordered pair)` combination.
  - Enforced: some distinct voter pair is selected, and each selected voter has at least one decisive pair witness.
  - Enforced decisiveness with profile-local binary implications over the selected voter’s preference direction.
- `encoding/axioms/asymm.py`, `encoding/axioms/no_cycle3.py`, `encoding/axioms/no_cycle4.py`
  - Retargeted to `FiniteSchema` with unchanged clause skeletons.
- `scripts/gen_dimacs.py`
  - Switched generation to a streaming clause writer so `(2,5)` can be emitted without holding all clauses in memory.
  - Added `--minlib-mode auto|selectors_v1|pair_selectors_v1`.
  - `auto` preserves the exact Sen24 artifact at `(2,4)` and selects parametric `minlib` elsewhere.
- `scripts/check_parametric_cnf.py`
  - Added a generalized auditor for `sen24` and `finite_schema_v1` manifests.
  - Checks schema dimensions, variable ranges, profile/pair/triple/quad discipline, per-family clause shapes, and expected counts.

---

## Semantic notes

### `un`

`un` is treated as **Unanimity / Weak Pareto**, not Universal Domain.  
The generalized encoder now quantifies over `schema.voters` through `schema.all_voters_prefer(...)`, so `(3,4)` no longer reuses hidden two-slot logic.

### `minlib`

The new parametric encoding uses:

- one auxiliary selector for each unordered pair of distinct voters, and
- one auxiliary decisive-witness variable for each `(voter, ordered alternative pair)`.

This directly encodes:

- existence of two distinct decisive voters,
- at least one decisive pair witness for each selected voter,
- profile-local decisiveness implications without fixed names such as `pref0/pref1` or `sel0/sel1`.

For Sen24 compatibility, the legacy `selectors_v1` layout is still the default only for `(2,4)`.  
The generalized schema path can also be instantiated at `(2,4)` via `--minlib-mode pair_selectors_v1`.

### `no_cycle3` / `no_cycle4`

These remain **local forbidden-pattern approximations**, not full `SocialAcyclic`.

- `no_cycle3` prohibits profile-local directed 3-cycles over ordered triples of distinct alternatives.
- `no_cycle4` prohibits profile-local directed 4-cycles over ordered 4-tuples of distinct alternatives.
- At `m=5`, `no_cycle3 ∧ no_cycle4` still allows length-5 cycles, so Step 0 confirms schema uniformity but does not by itself clear the later claim-scope question.

---

## Audited evidence snapshot

These runs were generated and audited on 2026-03-31.

| Case | Encoding | `minlib` mode | `nvars` | `nclauses` | CNF SHA-256 |
|---|---|---:|---:|---:|---|
| `(2,4)` legacy compatibility | `sen24` | `selectors_v1` | 6936 | 50114 | `34f5da1bae5b9425125de8273b4c0a7b36116ab22ee4bd19a4b3cc544c00507f` |
| `(2,4)` generalized schema | `finite_schema_v1` | `pair_selectors_v1` | 6937 | 50115 | `116a50bf2027413adc96caf9fa1b286aaffa8b339a15bec4ae8ab8e8c53c81c8` |
| `(2,5)` generalized schema | `finite_schema_v1` | `pair_selectors_v1` | 288041 | 3528003 | `38bb5ac40c08424e4fa54cc2c225dc02adcbb30050dd15cb86d968b241d50bc0` |
| `(3,4)` generalized schema | `finite_schema_v1` | `pair_selectors_v1` | 165927 | 1347847 | `a7534bd9e70d53db1057c24a1538075f138d167fc61aa46213bf2a8c6046eb0d` |

Category counts for the two neighboring cases:

| Case | `asymm` | `un` | `minlib` | `no_cycle3` | `no_cycle4` |
|---|---:|---:|---:|---:|---:|
| `(2,5)` | 288000 | 72000 | 576003 | 864000 | 1728000 |
| `(3,4)` | 165888 | 20736 | 497671 | 331776 | 331776 |

---

## Commands used

Legacy Sen24 compatibility check:

```bash
python3 scripts/gen_dimacs.py \
  --n 2 --m 4 \
  --axioms asymm,un,minlib,no_cycle3,no_cycle4 \
  --out /tmp/sen24_step0_smoke.cnf \
  --manifest /tmp/sen24_step0_smoke.manifest.json

python3 scripts/check_sen24_cnf.py \
  /tmp/sen24_step0_smoke.cnf \
  --manifest /tmp/sen24_step0_smoke.manifest.json \
  --strict-duplicates \
  --fail-on-tautology
```

Generalized `(2,4)` base-size run:

```bash
python3 scripts/gen_dimacs.py \
  --n 2 --m 4 \
  --minlib-mode pair_selectors_v1 \
  --axioms asymm,un,minlib,no_cycle3,no_cycle4 \
  --out /tmp/schema_n2m4_param.cnf \
  --manifest /tmp/schema_n2m4_param.manifest.json

python3 scripts/check_parametric_cnf.py \
  /tmp/schema_n2m4_param.cnf \
  --manifest /tmp/schema_n2m4_param.manifest.json \
  --strict-duplicates \
  --fail-on-tautology
```

Neighboring cases:

```bash
python3 scripts/gen_dimacs.py \
  --n 2 --m 5 \
  --axioms asymm,un,minlib,no_cycle3,no_cycle4 \
  --out /tmp/schema_n2m5.cnf \
  --manifest /tmp/schema_n2m5.manifest.json

python3 scripts/check_parametric_cnf.py \
  /tmp/schema_n2m5.cnf \
  --manifest /tmp/schema_n2m5.manifest.json \
  --strict-duplicates \
  --fail-on-tautology

python3 scripts/gen_dimacs.py \
  --n 3 --m 4 \
  --axioms asymm,un,minlib,no_cycle3,no_cycle4 \
  --out /tmp/schema_n3m4.cnf \
  --manifest /tmp/schema_n3m4.manifest.json

python3 scripts/check_parametric_cnf.py \
  /tmp/schema_n3m4.cnf \
  --manifest /tmp/schema_n3m4.manifest.json \
  --strict-duplicates \
  --fail-on-tautology
```
