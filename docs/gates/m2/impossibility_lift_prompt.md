# M2 Impossibility-Lift Prompt (staged)

AI instruction sheet for proving the M2 positive bridge theorem `sen_impossibility_lifts`
in the `Sen-Lean4` repository. Use the two stages in order. Stage 1 produces a plan and must
typecheck without `sorry`; Stage 2 produces the complete proof. Decisions are recorded in
`docs/gates/m2/aim_signoff.md`.

The scope wall is **not** primarily between theorem families; it is between the Lean Proof layer
(which reaches full `SocialAcyclic`) and the CNF Witness/Audit layer (which certifies only the
sen24-audited short-cycle encoding). The Lean task below establishes the Proof-layer lift to full
acyclicity. Do NOT claim the CNF `no_cycle3/no_cycle4` witness lifts to full `SocialAcyclic` for
`m ≥ 5`.

---

## Confirmed semantic signatures (do not re-derive; match these exactly)

```lean
-- SocialChoiceAtlas/Core/Profile.lean
def Profile := Voter → Ranking Alt
def SWF := Profile Voter Alt → (Alt → Alt → Prop)
def prefers_i (p : Profile Voter Alt) (i : Voter) (x y : Alt) : Prop := (p i).prefers x y

-- SocialChoiceAtlas/Core/Basics.lean
def strictPart (R : α → α → Prop) (x y : α) : Prop := R x y ∧ ¬ R y x
def cycle3 (S) : Prop := ∃ a b c, a ≠ b ∧ b ≠ c ∧ c ≠ a ∧ S a b ∧ S b c ∧ S c a
def cycle4 (S) : Prop := ∃ a b c d, a ≠ b ∧ b ≠ c ∧ c ≠ d ∧ d ≠ a ∧ S a b ∧ S b c ∧ S c d ∧ S d a
def Acyclic (S) : Prop := ∀ a, ¬ Relation.TransGen S a a
theorem cycle3_implies_not_acyclic {S} (h : cycle3 S) : ¬ Acyclic S
theorem cycle4_implies_not_acyclic {S} (h : cycle4 S) : ¬ Acyclic S
theorem strictPart_asymm (R) (x y) : strictPart R x y → ¬ strictPart R y x

-- SocialChoiceAtlas/Axioms/Pareto.lean
def UN (F : SWF Voter Alt) : Prop :=
  ∀ p x y, (∀ i, prefers_i p i x y) → strictPart (F p) x y

-- SocialChoiceAtlas/Axioms/Liberalism.lean
def Decisive (F) (i : Voter) (x y : Alt) : Prop :=
  ∀ p, (prefers_i p i x y → strictPart (F p) x y) ∧
       (prefers_i p i y x → strictPart (F p) y x)
def MINLIB (F : SWF Voter Alt) : Prop :=
  ∃ i j : Voter, i ≠ j ∧
    ∃ x y z w : Alt, x ≠ y ∧ z ≠ w ∧ Decisive F i x y ∧ Decisive F j z w
theorem Decisive.symm (h : Decisive F i x y) : Decisive F i y x

-- SocialChoiceAtlas/Axioms/Rationality.lean
def SocialAcyclic (F : SWF Voter Alt) : Prop := ∀ p, Acyclic (strictPart (F p))
```

The base-case proof to PORT (do not re-prove): `SocialChoiceAtlas/Sen/BaseCase24/Theorem.lean`,
especially `sen_not_acyclic_01` (the 3-case analysis: 2-overlap → contradiction, 1-overlap →
`cycle3`, disjoint → `cycle4`), `sen_not_acyclic`, and `sen_impossibility_basecase`. Helpers there:
`profile2`, `mkRanking4`, `prefers_i_profile2_voter{0,1}`, `beq_false_of_ne`.

---

## Target theorem

```lean
theorem sen_impossibility_lifts
    {n m : ℕ} (hn : 2 ≤ n) (hm : 4 ≤ m)
    (F : SWF (Fin n) (Fin m))
    (hUN : UN F) (hMINLIB : MINLIB F) :
    ¬ SocialAcyclic F
```

The statement may be minimally adjusted to typecheck against the current definitions, but the
mathematical content must NOT weaken: any finite case with at least two voters and at least four
alternatives satisfying semantic `UN` and `MINLIB` cannot be `SocialAcyclic`.

---

## Placement and build (from Decision 3)

- New module: `SocialChoiceAtlas/Sen/Lifting/ImpossibilityLift.lean`.
- It has NO solver backend, so it MUST be added to the `SocialChoiceAtlas.lean` root import list so
  default `lake build` exercises it on every PR. Do NOT make it opt-in like `Case11111` /
  `SATSenCNF`.
- Do NOT modify the CNF encoder, SAT artifacts, or M1/M1.5 paper claims in this task.
- Do NOT change existing base-case theorem statements unless absolutely necessary.

---

## Named obstacle — read before planning (this is where agents stall)

`MINLIB` does NOT guarantee that `x, y, z, w` are four distinct alternatives; the decisive pairs may
overlap. That is precisely why `sen_not_acyclic_01` case-splits on overlap. The base-case proof
completes its 4-point cycle pattern by pulling the missing alternative(s) from `Finset.univ.erase`,
relying on `Fintype.card (Fin 4) = 4`. At the larger case you must instead prove, from
`hm : 4 ≤ m`, that the alternatives needed to complete the relevant cycle still EXIST in `Fin m`
(a `4 ≤ Fintype.card`-style completion lemma). This lemma is purely technical, unrelated to the
scope wall, and is the single most likely stall point. It MUST appear in the Stage 1 risk list.

Note also: `MINLIB` supplies the two distinct decisive voters directly (no need to manufacture
canonical `Fin n` indices from `hn` unless the witness voters are insufficient). Prefer the
witness-supplied voters/alternatives over hand-built `Fin` indices.

---

## STAGE 1 — plan and helper inventory (NO full proof yet)

Do NOT implement the full proof. Inspect the existing Sen semantic layer and produce an
implementation plan for `sen_impossibility_lifts`.

Required output:
1. The exact theorem statement that typechecks against current definitions.
2. Whether `MINLIB` already supplies the required voters AND four sufficiently-distinct
   alternatives, or whether the missing alternatives must be constructed from `hm` (state which,
   citing the overlap case-split).
3. The minimal helper lemmas needed, each with its statement, including the
   `4 ≤ Fintype.card (Fin m)` completion lemma named in the obstacle section.
4. Which lemmas/constructions in `Theorem.lean` are PORTED verbatim vs. re-stated polymorphically
   (`sen_not_acyclic_01` logic, `profile2` lift, `cycle{3,4}_implies_not_acyclic`).
5. A risk list of Lean-specific obstacles. The completion lemma above MUST be on it.

You may add comments or skeleton declarations ONLY if they compile. Do NOT leave `sorry`, `admit`,
or unresolved `aesop?`/`exact?` in committed code, even at Stage 1.

Report: files inspected; the plan; the narrowest build command that typechecks any skeleton you
committed.

---

## STAGE 2 — complete proof (after the Stage 1 plan is approved)

Implement the helper lemmas and the final theorem from the approved plan.

Build the proof by small lemmas rather than one monolithic proof. Expected strategy:
1. From `hMINLIB`, obtain the two distinct decisive voters and their decisive pairs.
2. From `hm : 4 ≤ m`, obtain/complete the four-alternative pattern (completion lemma).
3. Reconstruct the larger-case profile embedding the base-case preference pattern on the selected
   voters/alternatives (lift `profile2`).
4. Port the `sen_not_acyclic_01` case analysis to derive the social strict edges from `hUN` and the
   `Decisive` hypotheses (re-state polymorphically; do not re-prove the social-choice content).
5. Assemble `cycle3`/`cycle4` and apply `cycle{3,4}_implies_not_acyclic`.
6. Contradict `SocialAcyclic F` via the offending profile.

Hard constraints:
- No `sorry` / `admit` / unsolved goals / leftover search-tactic placeholders in the new module.
- Do NOT weaken the theorem.
- Do NOT touch CNF artifacts or M1/M1.5 claims.
- Add the module to the `SocialChoiceAtlas.lean` root import (Decision 3).

Deliverables:
A. Files modified/created.
B. Exact final theorem statement as committed.
C. List of helper lemmas introduced.
D. Explicit confirmation: no `sorry`, `admit`, or unsolved goal in the new lifting module
   (e.g. `grep -RIn "sorry\|admit" SocialChoiceAtlas/Sen/Lifting/` returns nothing).
E. Commands run, including `lake build` (or the narrowest target that checks the new module) and
   its result.

---

## Scope-wall documentation (create alongside the proof)

Create `docs/m2_scope_wall.md` stating:
- The Lean Proof layer establishes a semantic Sen impossibility lift to full `SocialAcyclic`
  (the theorem above).
- The sen24 CNF Witness/Audit layer certifies a short-cycle encoding (`no_cycle3 ∧ no_cycle4`)
  whose equivalence to full acyclicity was audited only for four alternatives, by exhaustive finite
  check in `scripts/check_acyclicity_short_cycles.py`.
- Therefore the M2 scope wall is between the Proof layer and the Witness/Audit layer, not merely
  between local-rationality and full-acyclicity theorem families. For `m ≥ 5` the audited
  equivalence does not transfer automatically, so the proof-level lift does not upgrade the CNF
  atlas into a family-level CNF certificate.

Non-goals (restate in the doc): do not claim the CNF `no_cycle` witness lifts to full
`SocialAcyclic` for `m ≥ 5`; no new solver experiments; no changes to M1/M1.5 claims.
