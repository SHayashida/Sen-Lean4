# M2 Stage 1 — Impossibility Lift Plan

**Module to create:** `SocialChoiceAtlas/Sen/Lifting/ImpossibilityLift.lean`  
**Imported from:** `SocialChoiceAtlas.lean` (root, default `lake build`)  
**Goal:** Prove `sen_impossibility_lifts` — Sen's impossibility lifts from the
`(Fin 2, Fin 4)` base case to any finite case with at least two voters and at
least four alternatives, in the **Lean Proof layer** (not the CNF Witness/Audit
layer; see `docs/m2_scope_wall.md`).

This file is the Stage 1 plan: theorem statement, helper-lemma inventory,
porting plan, and risk list. The Stage 1 commit installs only the module
shell (compilable, no `sorry`/`admit`) plus the most bounded helper lemma; the
remainder is implemented in Stage 2.

## Files inspected

- `SocialChoiceAtlas/Core/Basics.lean` — `strictPart`, `cycle3`, `cycle4`,
  `Acyclic`, `cycle{3,4}_implies_not_acyclic`, `strictPart_asymm`,
  `strictPart_irrefl`.
- `SocialChoiceAtlas/Core/Profile.lean` — `Profile`, `SWF`, `prefers_i`
  (polymorphic over `Voter`, `Alt`; `[DecidableEq Alt] [Fintype Alt]`).
- `SocialChoiceAtlas/Core/Ranking.lean` — `Ranking` (Nodup list + complete);
  `prefers`, `position`, `prefers_irrefl/trans/asymm/total`, `length_eq_card`.
- `SocialChoiceAtlas/Axioms/Pareto.lean` — `UN F`.
- `SocialChoiceAtlas/Axioms/Liberalism.lean` — `Decisive F i x y`, `MINLIB F`,
  `Decisive.symm`.
- `SocialChoiceAtlas/Axioms/Rationality.lean` — `SocialAcyclic F`.
- `SocialChoiceAtlas/Sen/BaseCase24/Spec.lean` — `abbrev Voter := Fin 2`,
  `abbrev Alt := Fin 4`, `Profile24`, `SWF24`.
- `SocialChoiceAtlas/Sen/BaseCase24/Theorem.lean` — `profile2`, `mkRanking4`,
  `prefers_i_profile2_voter{0,1}`, `MINLIBWitness`, `sen_not_acyclic_01`
  (the 3-case overlap analysis), `sen_not_acyclic`, `sen_impossibility_basecase`.
- `SocialChoiceAtlas.lean` — root import list (no opt-in for solver modules).
- `lakefile.lean` — `globs := #[\`SocialChoiceAtlas]`; only files under
  `SocialChoiceAtlas/` are kernel-checked by default `lake build`.
- Mathlib v4.15.0: `Fintype.card_fin`, `Finset.card_lt_iff_ne_univ`,
  `Finset.card_erase_of_mem`, `Finset.eq_univ_iff_forall`,
  `List.toFinset_card_of_nodup`.

## 1. Exact theorem statement (typechecks against current defs)

The statement in the prompt typechecks as-is, given the polymorphic axiom
signatures. We will commit it (with proof) at Stage 2:

```lean
theorem sen_impossibility_lifts
    {n m : ℕ} (hn : 2 ≤ n) (hm : 4 ≤ m)
    (F : SWF (Fin n) (Fin m))
    (hUN : UN F) (hMINLIB : MINLIB F) :
    ¬ SocialAcyclic F
```

No instance arguments are needed: `Fin m` already has `DecidableEq` and
`Fintype` instances from Mathlib, matching the implicit instance demands on
`SWF`/`Profile`/`UN`/`MINLIB`/`SocialAcyclic`.

The hypothesis `hn : 2 ≤ n` is logically redundant given that `MINLIB`
already supplies two distinct voters in `Fin n` (so `Fin n` is nonempty and
has cardinality ≥ 2). It is kept for symmetry with the human statement of
Sen's theorem and because removing it would slightly weaken what the
statement *advertises* even though the math is unchanged. If it turns out to
be a build-time obstacle (e.g. unused-arg lint), it may be dropped at Stage 2
without weakening the math.

## 2. Does `MINLIB` supply four distinct alternatives?

**No.** `MINLIB` supplies:

- two distinct voters `i ≠ j` (always usable directly; do NOT manufacture
  canonical `Fin n` indices from `hn`);
- a decisive pair `(x, y)` with `x ≠ y` for voter `i`;
- a decisive pair `(z, w)` with `z ≠ w` for voter `j`.

It does **not** assert `{x, y} ∩ {z, w} = ∅`. The pairs may overlap. This is
exactly why `sen_not_acyclic_01` case-splits on overlap:

- **Case 1 (two-point overlap, `{x,y} = {z,w}`):** the two decisive voters
  force opposite social preferences on the same pair, so
  `strictPart_asymm` yields `False` directly. No completion needed.
- **Case 2 (one-point overlap, exactly one of `z,w` equals one of `x,y`):**
  three distinct alternatives are in hand; the cycle is `cycle3`. We need
  **one** fresh alternative `t ∉ {x, y, z}` to complete the rankings (the
  rankings are length-4 in the base case; at larger `m`, we instead need a
  ranking whose first three positions are the cycle vertices, plus a tail
  that covers the rest of `Fin m`).
- **Case 3 (disjoint pairs):** all four `x, y, z, w` distinct; the cycle is
  `cycle4`. No additional alternative is needed for the cycle itself, but
  at larger `m` we still need to complete the rankings beyond position 4.

Hence the missing alternatives at the lift case **must be constructed from
`hm : 4 ≤ m`** by a fresh-element / ranking-completion lemma.

## 3. Helper lemma inventory (minimal, in dependency order)

All helpers live in `SocialChoiceAtlas/Sen/Lifting/ImpossibilityLift.lean`
under namespace `SocialChoiceAtlas.Sen.Lifting`.

### H1 — Existence of a fresh element when a finset is not the universe

```lean
lemma exists_not_mem_of_card_lt
    {α : Type*} [DecidableEq α] [Fintype α]
    {s : Finset α} (h : s.card < Fintype.card α) :
    ∃ a : α, a ∉ s
```

Proof sketch: `Finset.card_lt_iff_ne_univ` gives `s ≠ univ`; then
`Finset.eq_univ_iff_forall` (contrapositive) extracts the witness. This is
the **completion lemma named in the obstacle section** and is the only
new Mathlib-style fact required. **This lemma is committed at Stage 1.**

### H2 — `4 ≤ Fintype.card (Fin m)` from `4 ≤ m`

```lean
lemma four_le_card_fin {m : ℕ} (hm : 4 ≤ m) : 4 ≤ Fintype.card (Fin m)
```

Proof: `Fintype.card_fin m` rewrites the goal to `4 ≤ m`. One-liner.

### H3 — Ranking completion from a Nodup prefix

```lean
lemma mkRankingOfPrefix
    {α : Type*} [DecidableEq α] [Fintype α]
    (l : List α) (hnodup : l.Nodup) :
    ∃ r : Ranking α, ∀ k : ℕ, ∀ h : k < l.length,
      r.position (l.get ⟨k, h⟩) = k
```

Or, more directly, a *constructive* version that returns the ranking and a
proof that `l` is a prefix of `r.toList`. The list used is
`l ++ (Finset.univ \ l.toFinset).toList`; `Nodup` of this list follows from
`l.Nodup`, `Nodup` of `toList` of a finset, and disjointness from
`mem_sdiff`. Completeness follows from `mem_union`.

Practical signature (preferred — avoids existentials at use sites):

```lean
def rankingOfPrefix
    {α : Type*} [DecidableEq α] [Fintype α]
    (l : List α) (hnodup : l.Nodup) : Ranking α

lemma rankingOfPrefix_position_lt
    {α : Type*} [DecidableEq α] [Fintype α]
    (l : List α) (hnodup : l.Nodup) (k : ℕ) (h : k < l.length) :
    (rankingOfPrefix l hnodup).position (l.get ⟨k, h⟩) = k

lemma rankingOfPrefix_prefers
    {α : Type*} [DecidableEq α] [Fintype α]
    (l : List α) (hnodup : l.Nodup)
    {i j : ℕ} (hi : i < l.length) (hj : j < l.length) (hij : i < j) :
    (rankingOfPrefix l hnodup).prefers (l.get ⟨i, hi⟩) (l.get ⟨j, hj⟩)
```

This is the **polymorphic generalization** of `mkRanking4` from
`Theorem.lean:96`.

### H4 — Two-voter profile lift

```lean
def profile2On {n : ℕ} {α : Type*} [DecidableEq α] [Fintype α]
    (i j : Fin n) (r_i r_j : Ranking α)
    (rest : Fin n → Ranking α) :
    Profile (Fin n) α
```

Returns the profile that assigns `r_i` to `i`, `r_j` to `j`, and `rest k` to
any other voter `k`. Lemmas:

```lean
lemma profile2On_apply_i ... : profile2On i j r_i r_j rest i = r_i
lemma profile2On_apply_j (hij : i ≠ j) ... : profile2On i j r_i r_j rest j = r_j
@[simp] lemma prefers_i_profile2On_at_i (a b : α) :
    prefers_i (profile2On i j r_i r_j rest) i a b ↔ r_i.prefers a b
@[simp] lemma prefers_i_profile2On_at_j (hij : i ≠ j) (a b : α) :
    prefers_i (profile2On i j r_i r_j rest) j a b ↔ r_j.prefers a b
```

To realize `rest`, we use a constant default — e.g. `rankingOfPrefix []
List.nodup_nil` — so the auxiliary voters have *some* ranking; their
preferences will be irrelevant in the unanimity arguments below because the
profile only needs `UN`-relevant agreement on **specific** pairs, and the
proof either constructs those pairs to agree on all voters by design or
uses only the two decisive voters' preferences via `Decisive`.

(Actually: the existing base case proves `hall_zx : ∀ v, prefers_i p v z x`
across both `Fin 2` voters because both rankings agree on `z > x` by
design. In the lift, we must extend this to "all `n` voters agree", which
means the **rest** rankings must also place `z > x`. Hence `rest` cannot be
truly arbitrary — it must be chosen to agree on the relevant unanimity
pairs. Concretely, we choose `rest k = r_i` for all `k ≠ i, j` so the
unanimity arguments degenerate to two-voter unanimity. This is recorded
in the risk list, R3.)

Revised practical signature:

```lean
def liftProfile {n : ℕ} {α : Type*} [DecidableEq α] [Fintype α]
    (i : Fin n) (r_i r_j : Ranking α) (j : Fin n) : Profile (Fin n) α :=
  fun k => if k = j then r_j else r_i
```

This makes every non-`j` voter use `r_i`, including `i`. So
`prefers_i (liftProfile i r_i r_j j) i a b ↔ r_i.prefers a b`
(by `i ≠ j` from `MINLIB`),
and `prefers_i (liftProfile i r_i r_j j) j a b ↔ r_j.prefers a b`,
and `prefers_i (liftProfile i r_i r_j j) k a b ↔ r_i.prefers a b` for
`k ≠ j`. Unanimity over all `n` voters then reduces to: `r_i` and `r_j`
both prefer `a` to `b`. This matches the base case's two-voter
unanimity arguments exactly.

### H5 — Sen lift: 3-case overlap analysis (polymorphic port)

The actual main proof. It will be split into one private lemma per case
(mirroring the existing `sen_not_acyclic_01` structure):

```lean
private lemma sen_lift_case_two_overlap
    {n m : ℕ} (hm : 4 ≤ m) (F : SWF (Fin n) (Fin m))
    (hUN : UN F) {i j : Fin n} (hij : i ≠ j)
    {x y z w : Fin m}
    (hxy : x ≠ y) (hzw : z ≠ w)
    (hdec_i : Decisive F i x y) (hdec_j : Decisive F j z w)
    (hzw_eq : (z = x ∧ w = y) ∨ (z = y ∧ w = x)) :
    ¬ SocialAcyclic F

private lemma sen_lift_case_one_overlap
    {n m : ℕ} (hm : 4 ≤ m) (F : SWF (Fin n) (Fin m))
    (hUN : UN F) {i j : Fin n} (hij : i ≠ j)
    {x y z w : Fin m}
    (hxy : x ≠ y) (hzw : z ≠ w)
    (hdec_i : Decisive F i x y) (hdec_j : Decisive F j z w)
    -- exactly one of {z, w} is in {x, y}
    (hOverlap : (z ∈ ({x, y} : Finset (Fin m)) ∧ w ∉ ({x, y} : Finset (Fin m))) ∨
                (w ∈ ({x, y} : Finset (Fin m)) ∧ z ∉ ({x, y} : Finset (Fin m)))) :
    ¬ SocialAcyclic F

private lemma sen_lift_case_disjoint
    {n m : ℕ} (hm : 4 ≤ m) (F : SWF (Fin n) (Fin m))
    (hUN : UN F) {i j : Fin n} (hij : i ≠ j)
    {x y z w : Fin m}
    (hxy : x ≠ y) (hzw : z ≠ w)
    (hdec_i : Decisive F i x y) (hdec_j : Decisive F j z w)
    (hzx : z ≠ x) (hzy : z ≠ y) (hwx : w ≠ x) (hwy : w ≠ y) :
    ¬ SocialAcyclic F
```

Strategy is identical to the base case but uses `rankingOfPrefix` (H3)
to extend the 4-element prefix to a `Ranking (Fin m)`, and `liftProfile`
(H4) to extend the 2-voter profile to an `n`-voter profile.

### H6 — Main theorem assembly

```lean
theorem sen_impossibility_lifts
    {n m : ℕ} (hn : 2 ≤ n) (hm : 4 ≤ m)
    (F : SWF (Fin n) (Fin m))
    (hUN : UN F) (hMINLIB : MINLIB F) :
    ¬ SocialAcyclic F
```

Proof: destruct `hMINLIB`; case-split on `z ∈ {x,y}` and `w ∈ {x,y}`;
dispatch to H5's three private lemmas.

## 4. Ported verbatim vs. re-stated polymorphically

| Item | Treatment | Source |
|---|---|---|
| `strictPart`, `cycle3`, `cycle4`, `Acyclic` | already polymorphic, used as-is | `Core/Basics.lean` |
| `cycle3_implies_not_acyclic`, `cycle4_implies_not_acyclic` | already polymorphic, used as-is | `Core/Basics.lean` |
| `strictPart_asymm`, `strictPart_irrefl` | already polymorphic, used as-is | `Core/Basics.lean` |
| `UN`, `MINLIB`, `Decisive`, `Decisive.symm`, `SocialAcyclic` | already polymorphic, used as-is | `Axioms/*.lean` |
| `Ranking`, `Ranking.prefers`, `Ranking.position` | already polymorphic, used as-is | `Core/Ranking.lean` |
| `mkRanking` (list constructor) | already polymorphic, used as-is | `Theorem.lean:43` |
| `mkRanking4` (4-element constructor with `Fintype.card Alt = 4`) | **NOT reused.** Replaced by `rankingOfPrefix` (H3), which works for any `α` with `4 ≤ Fintype.card α`. | `Theorem.lean:96` |
| `profile2` (two-voter, `Voter = Fin 2`) | **NOT reused.** Replaced by `liftProfile` (H4) for arbitrary `Fin n`. | `Theorem.lean:59` |
| `prefers_i_profile2_voter{0,1}` | replaced by analogous `prefers_i_liftProfile_at_{i,j}` lemmas. | `Theorem.lean:68-74` |
| `beq_false_of_ne`, `beq_true` | not reused in the lift (`rankingOfPrefix` is defined without `List.indexOf_cons`-style unfolding). | `Theorem.lean:84-93` |
| `MINLIBWitness`, `extractWitness` | not reused; we destructure `hMINLIB` directly via `rcases`. | `Theorem.lean:120,134` |
| `sen_not_acyclic_01` 3-case logic | **re-stated polymorphically** as H5 (three private case lemmas). The *structure* of the argument (the cycle pattern in each case, which `Decisive` call lands which strict edge, which alternatives the unanimity step uses) is preserved verbatim; only the ranking/profile construction is generalized. | `Theorem.lean:166` |
| `sen_not_acyclic`, `sen_impossibility_basecase` | not reused; their `fin_cases i <;> fin_cases j` enumeration is `Fin 2`-specific. The lift's main theorem dispatches differently. | `Theorem.lean` |

## 5. Risk list (Lean-specific obstacles)

R1. **(Named obstacle from the prompt.)** Completing the 4-alternative
pattern at the lift case. `MINLIB` does not guarantee `{x,y,z,w}` are four
distinct, so the disjoint and 1-overlap cases must construct fresh
alternatives from `hm : 4 ≤ m`. The mathematical content is supplied by
H1 (`exists_not_mem_of_card_lt`) and H3 (`rankingOfPrefix`). **The Lean
risk is in H3:** proving that `l ++ (Finset.univ \ l.toFinset).toList` is
`Nodup` and complete requires careful `simp` lemmas on `toList` and
`mem_sdiff`. **Mitigation:** keep the construction explicit (no clever
`decide`/`simp` reliance), and prove `Nodup` from `List.Nodup.append` +
`Finset.toList_nodup` + a disjointness lemma derived from `mem_sdiff`.

R2. **`Ranking.position` and `Ranking.prefers` unfolding.** The base case
proves preference facts like `prefers_i p voter0 x y` by `simp
[Ranking.prefers, Ranking.position, ..., List.indexOf_cons, beq_true,
beq_false_of_ne, ...]`. At the lift we cannot use the same `decide`-style
discharge because `m` is symbolic. **Mitigation:** state `rankingOfPrefix`
*positionally* (H3's `_position_lt` and `_prefers` lemmas) so callers
never need to unfold `List.indexOf` — they consume H3's API.

R3. **Unanimity over `n` voters vs. two-voter agreement in the base case.**
The base case proves `hall_zx : ∀ v : Voter, prefers_i p v z x` by
`fin_cases v` over `Fin 2` and explicit ranking unfolding. At the lift we
have `n` voters, so the proof shape must change: design `liftProfile` so
that every non-`j` voter (including `i`) uses ranking `r_i`. Then
`prefers_i (liftProfile i r_i r_j j) k a b` reduces to `r_i.prefers a b`
for any `k ≠ j`, and to `r_j.prefers a b` for `k = j`. The "all voters
prefer `a` to `b`" goal becomes a 2-part check (`r_i` and `r_j` both
prefer `a` to `b`), identical in content to the base case. **Mitigation:**
keep `liftProfile` simple (`if k = j then r_j else r_i`); prove
`unanimity_lift : (r_i.prefers a b ∧ r_j.prefers a b) → ∀ k : Fin n,
prefers_i (liftProfile i r_i r_j j) k a b` as a one-line helper.

R4. **`Decisive` symmetry at the lift.** The base-case 1-overlap subcases
use `Decisive.symm` and the second component of `Decisive` (the
`prefers_i p i y x → strictPart (F p) y x` branch). Both are polymorphic
and used as-is; **no new risk**, but the call pattern must be ported
carefully. **Mitigation:** mirror the base-case proof line-by-line in each
H5 sub-lemma.

R5. **`fin_cases` over `Fin n` (symbolic n).** The base case dispatches
`fin_cases i <;> fin_cases j` over `Fin 2`. We cannot do that for symbolic
`n`. **Mitigation:** do not dispatch on voter indices; use the witnesses
`i, j` from `MINLIB` directly as opaque `Fin n` values with `i ≠ j`.
This is exactly what the prompt's note (`MINLIB supplies the two distinct
decisive voters directly`) prescribes.

R6. **Instance hygiene for `SWF`/`Profile` on `Fin m`.** The polymorphic
`SWF (Fin n) (Fin m)` needs `[DecidableEq (Fin m)] [Fintype (Fin m)]`
visible at use sites. **Mitigation:** these instances are global from
Mathlib; no opening or local instance binding is needed. Verified by
inspecting `Profile.lean` (line 18) which uses `[DecidableEq Alt]
[Fintype Alt]` as `variable` bindings.

R7. **Mathlib lemma name drift at v4.15.0.** I plan to use
`Finset.card_lt_iff_ne_univ`, `Finset.eq_univ_iff_forall`,
`Finset.card_erase_of_mem`, `List.toFinset_card_of_nodup`,
`Fintype.card_fin`, `List.Nodup.append`. All confirmed present in the
vendored Mathlib (`grep` in `.lake/packages/mathlib/Mathlib/Data/`). **No
additional risk beyond the lemma-by-lemma checks above.**

R8. **`autoImplicit false` discipline.** `lakefile.lean:6` sets
`autoImplicit, false`. All type variables in helper lemmas must be
explicitly bound (`{α : Type*}` etc.). **Mitigation:** every helper in
H1–H6 above already lists its implicits explicitly.

R9. **Build cost.** The lift module imports Mathlib (via the core
modules); adding it to the default root import means every PR pays its
compilation cost. **Mitigation:** keep the module small; do not pull in
heavy Mathlib subtrees beyond what `Core/*.lean` and `Axioms/*.lean`
already pull. Verified the new lemmas (H1–H5) only need
`Mathlib.Data.Finset.Card`, `Mathlib.Data.Fintype.Card`, and
`Mathlib.Data.List.*`, all already transitive imports.

## Stage 1 commit boundary

Stage 1 commits ONLY:
- `SocialChoiceAtlas/Sen/Lifting/ImpossibilityLift.lean` containing the
  module docstring, imports, namespace, and lemma H1
  (`exists_not_mem_of_card_lt`) **fully proved**. No other helpers, no
  main theorem, no `sorry`/`admit`/`exact?`/`aesop?`.
- An updated `SocialChoiceAtlas.lean` adding the new module to the root
  import list (Decision 3).
- `docs/m2_scope_wall.md` is written at Stage 2 alongside the main proof;
  Stage 1 records the plan only.

Stage 2 implements H2–H6, completes the main theorem, and adds the
scope-wall doc.

## Narrowest build command for Stage 1

```
lake build SocialChoiceAtlas.Sen.Lifting.ImpossibilityLift
```

This compiles the new module and (transitively) the core/axiom
dependencies, but does not pull in the optional `Case11111`/`SATSenCNF`
modules.
