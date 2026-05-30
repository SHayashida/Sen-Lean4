# M2 Aim Sign-off

## Bridge Theorems / Transfer Contract — construction-readiness record

**Status:** Decisions 1, 2, and 3 LANDED on `codex/m2-bridge` (Stage 1+2: `sen_impossibility_lifts` kernel-checked at `SocialChoiceAtlas/Sen/Lifting/ImpossibilityLift.lean:558`; scope wall at `docs/m2_scope_wall.md`; `papers/m2/` scaffold landed; PR #6 promoted to ready). Decision 4 RATIFIED-DEFERRED to milestone **M2.1** as Negative #2.
**Branch context:** `codex/m2-bridge` (Stage 1+2 + `papers/m2/` scaffold landed).
**Program:** Auditable Abstraction Contracts — pillar M2 (Transfer Contract).
**Purpose of this file:** record the four blocking decisions that must be fixed before the
`SocialChoiceAtlas/Sen/Lifting/` skeleton and `papers/m2/` scaffold are generated, so that
construction does not require rework. This file is the single source of truth for M2's aim.

---

## Position in the four-contract program

| Pillar | Contract | Established result |
|---|---|---|
| M1 (`paper/`) | Evidence Contract | Finite Sen24 exploration is diagnosable via Proof (Lean-kernel LRAT replay) / Audit (CNF-manifest conformance) / Witness (SAT-model validation). Base case `(2,4)` is kernel-checked. |
| M1.5 (`papers/m1_5/`) | Explanation Contract | Under clause-multiset equivalence (≡CM), the raw lever-level minimal repair family is not canonical. |
| **M2 (`papers/m2/`)** | **Transfer Contract** | **THIS MILESTONE.** When does finite UNSAT/impossibility evidence at the base case lift to a case family? |
| M4 | Normative Contract (Repair Geometry) | Receives M2's negative repair-transfer results. |

A separate strand, β (Completion Contract), returned an **Axis-1 No-Go** (a hardness-flagship
route closed in the native-unweighted topology) and was demoted to a supporting chapter. β enters
M2 only as discipline, never as technical vocabulary:
- (β-1) no hardness/complexity flagship;
- (β-2) record BOTH sides of every boundary;
- (β-3) negative results are contract body, not appendix.

---

## Decision 1 — Refined flagship (CONFIRMED)

M2 ships **three** deliverables, not a single flagship. A single-side framing is rejected (β-2).

**Positive (conditional bridge theorem).**
> Sen's impossibility admits a semantic Lean-level lift from the Sen24 witness pattern to all
> finite cases with at least two voters and at least four alternatives, provided the larger case
> satisfies the same semantic axioms `UN`, `MINLIB`, and `SocialAcyclic`.

**Negative #1 (scope wall — MANDATORY, β-2).**
> The proof-level lift does NOT automatically upgrade the CNF atlas witness into a family-level
> CNF certificate. The CNF witness layer uses a short-cycle rationality encoding
> (`no_cycle3 ∧ no_cycle4`) whose equivalence to full acyclicity was audited only at sen24
> (four alternatives, by exhaustive finite check in `scripts/check_acyclicity_short_cycles.py`).
> For `m ≥ 5` that equivalence is not automatic.

**Negative #2 (Candidate-B representation non-canonicity).**
> Carry the M1.5 non-canonicity phenomenon to family scale: even where impossibility/repair
> *status* lifts, the *representation* under which repairs are reported (bundled vs. split,
> clause-equivalent re-encodings) need not transfer canonically. (Requires Decision 4.)

**One-sentence aim.** M2 is not "we generalized Sen24"; it is the study of *what lifts as Proof
and what stays in the Witness/Audit layer* when a finite atlas is bridged to general social choice.

---

## Decision 2 — Preservation property P (DESIGNED)

The repo's axiom layer is already **polymorphic in `Voter` and `Alt`**; `(2,4)` is just an
instantiation (`Voter := Fin 2`, `Alt := Fin 4`). The confirmed semantic signatures are:

```
-- SocialChoiceAtlas/Core/Profile.lean
def SWF := Profile Voter Alt → (Alt → Alt → Prop)
def prefers_i (p) (i) (x y) : Prop := (p i).prefers x y

-- SocialChoiceAtlas/Axioms/Pareto.lean
def UN (F : SWF Voter Alt) : Prop :=
  ∀ p x y, (∀ i, prefers_i p i x y) → strictPart (F p) x y

-- SocialChoiceAtlas/Axioms/Liberalism.lean
def Decisive (F) (i) (x y) : Prop :=
  ∀ p, (prefers_i p i x y → strictPart (F p) x y) ∧
       (prefers_i p i y x → strictPart (F p) y x)
def MINLIB (F : SWF Voter Alt) : Prop :=
  ∃ i j : Voter, i ≠ j ∧
    ∃ x y z w : Alt, x ≠ y ∧ z ≠ w ∧ Decisive F i x y ∧ Decisive F j z w

-- SocialChoiceAtlas/Axioms/Rationality.lean
def SocialAcyclic (F : SWF Voter Alt) : Prop := ∀ p, Acyclic (strictPart (F p))

-- SocialChoiceAtlas/Core/Basics.lean
def Acyclic (S) : Prop := ∀ a, ¬ Relation.TransGen S a a
def cycle3 / cycle4 : ...  (with cycle3_implies_not_acyclic, cycle4_implies_not_acyclic)
def strictPart (R) (x y) : Prop := R x y ∧ ¬ R y x
```

Because the axioms are polymorphic, the bridge does NOT redefine axioms at the larger case. P is
stated per-axiom, in two layers:

**P_lift (holds — the positive bridge hypothesis).**
An axiom A is liftable when its truth at the larger case implies its truth on the embedded
base-case sub-configuration, BECAUSE A is profile-universally quantified and the embedding extends
profiles. `UN` and `MINLIB` (hence `Decisive`) satisfy P_lift: `UN` quantifies over all profiles,
so it restricts to any embedded profile; `MINLIB` is itself an existential that the larger case
supplies. **This is the theorem-level explanation of the empirical Outcome A (16/16 lift).**

**P_wall (fails — the scope wall).**
The rationality side does NOT satisfy P_lift at the CNF/Witness layer. The CNF encodes
`no_cycle3 ∧ no_cycle4`, which is equivalent to `SocialAcyclic` only for `m ≤ 4` (audited finite
fact). For `m ≥ 5`, `¬(no_cycle3 ∧ no_cycle4)` is strictly stronger than `¬SocialAcyclic`
(it demands a short cycle), so the CNF witness does not certify the semantic `¬SocialAcyclic`
conclusion that the Lean proof reaches.

**Key inversion (the program-coherence payoff).** At the **Lean Proof layer**, impossibility lifts
to *full* `SocialAcyclic` with no upper bound on `m` (`MINLIB` supplies four distinct-enough
alternatives; `UN` restricts; the base-case cycle is reconstructed). The wall therefore is NOT
between theorem families — it is between the **Proof layer (reaches full acyclicity)** and the
**CNF Witness/Audit layer (certifies only the sen24-audited short-cycle encoding)**. This routes
M2's mandatory negative directly through M1's Evidence Contract (Proof/Witness separation), closing
the program's logical chain.

### Target theorem (statement may be minimally adjusted to typecheck; content must not weaken)

```lean
theorem sen_impossibility_lifts
    {n m : ℕ} (hn : 2 ≤ n) (hm : 4 ≤ m)
    (F : SWF (Fin n) (Fin m))
    (hUN : UN F) (hMINLIB : MINLIB F) :
    ¬ SocialAcyclic F
```

### Known Lean obstacle (must be a named risk, see prompt)

`MINLIB` does not guarantee that `{x,y,z,w}` are four *distinct* elements (the pairs may overlap —
this is exactly why the base-case proof `sen_not_acyclic_01` case-splits into 2-overlap / 1-overlap
/ disjoint). The base-case proof completes its 4-point pattern by pulling missing alternatives from
`Finset.univ.erase`, relying on `Fintype.card (Fin 4) = 4`. At the larger case this becomes a
**non-trivial lemma**: from `hm : 4 ≤ m`, the missing alternatives needed to complete the cycle
pattern still exist in `Fin m`. This `4 ≤ Fintype.card`-style completion lemma is the single most
likely place an AI agent stalls; it is purely technical and unrelated to the scope wall.

`sen_not_acyclic_01` and its case analysis should be **ported, not re-proved**: `UN`, `Decisive`,
`strictPart`, `profile2`, `cycle3_implies_not_acyclic`, `cycle4_implies_not_acyclic` are all
polymorphic, so the porting work is lifting `profile2` (two voters) onto the two selected voters of
`Fin n` and re-running the existing case logic.

---

## Decision 3 — Lake build policy (CONFIRMED: default import)

The lifting Lean definitions MUST live under `SocialChoiceAtlas/Sen/Lifting/`, NEVER only under
`papers/m2/`. SWE reason: `lakefile.lean` resolves only files under `SocialChoiceAtlas/` into the
`lean_lib` target; a `.lean` file under `papers/m2/` is not kernel-checked by `lake build` and
would silently fail Gate 0c without an error signal.

Necessary but not sufficient: the existing solver-backed modules (`Case11111`, `SATSenCNF`) are
deliberately NOT imported from the library root and are built only on explicit request. The M2
lifting module has **no solver backend** (it is a pure axiom-level proof), so it MUST be added to
the `SocialChoiceAtlas.lean` root import list, so CI's default `lake build` exercises it on every
PR. Treating it as opt-in like the LRAT modules would silently demote a Transfer-Contract theorem
to the gate level of an optional SAT certificate.

**Decision: default root import. Not opt-in.**

---

## Decision 4 — Candidate-B witness class (RATIFIED-DEFERRED: ships in M2.1, not M2)

**M2 vs. M2.1 split, ratified.** M2 ships as a coherent Transfer-Contract paper comprising
(i) the positive Lean Proof-layer semantic lift `sen_impossibility_lifts`, and
(ii) Negative #1, the Proof-vs-Witness/Audit scope wall (`docs/m2_scope_wall.md`).
Candidate-B / Negative #2 (representation non-canonicity at family scale) is deferred to a
separate milestone **M2.1** and does **not** receive a full main-results section in
`papers/m2/`; only a forward pointer to M2.1 is allowed in Discussion / Future Work.

**Blocking scope.** Decision 4 blocks **only M2.1 / Negative #2**. It does **not** block:

- PR #6 promotion to ready-for-review;
- the `papers/m2/` scaffold (positive lift + scope wall);
- the `sen_impossibility_lifts` kernel-checked theorem.

**What remains for M2.1.** Negative #2 requires fixing the witness class
(bundled vs. split vs. clause-equivalent re-encoding) and its generator interface before
exploration scripts proliferate. Until fixed, keep prototypes under
`scripts/exploration/candidate_b/`; promote to `scripts/` only after they stabilize like
`check_parametric_cnf.py` (CLI surface + `finite_schema_v1` manifest + parametric `(n,m)`).
The missing `docs/candidate_b_encoding_sensitivity.md` (referenced from
`docs/experiment_protocol_repair_liftability.md`) is to be authored as part of M2.1.

---

## ScopeWall: docs-first, not forced into Lean (recommended)

`ScopeWall.lean` should NOT be over-formalized at first. The scope wall is, at this stage, a
guarantee-boundary statement best made as a paper-facing proposition plus `docs/m2_scope_wall.md`,
in the lineage of M1.5's "finite witness legitimization ≠ repair presentation canonicality." The
Lean side delivers the positive lift to full `SocialAcyclic`; the wall is the *gap to the CNF
witness*, which is documented and audited, not (yet) a Lean theorem.

---

## Readiness gate — construction may proceed

| Decision | Status | Blocks construction? |
|---|---|---|
| 1. Three-deliverable flagship | CONFIRMED | no |
| 2. Preservation P (P_lift / P_wall) + target theorem + named obstacle | DESIGNED | no |
| 3. Default lake root import | CONFIRMED | no |
| 4. Candidate-B witness class | RATIFIED-DEFERRED → M2.1 | blocks **M2.1 / Negative #2 ONLY**; does NOT block PR #6, `papers/m2/`, or the positive lift theorem |

**Verdict: construction of `SocialChoiceAtlas/Sen/Lifting/ImpossibilityLift.lean` and
`docs/m2_scope_wall.md` may proceed now, using the staged prompt in
`docs/gates/m2/impossibility_lift_prompt.md`.**

Non-blocking recommendations before `papers/m2/` scaffold (Stage 1+2 already landed on
`codex/m2-bridge`): add a `scripts/ci_m2_smoke.sh` placeholder wired into `.github/workflows/ci.yml`;
author `docs/candidate_b_encoding_sensitivity.md` under Decision 4 (currently absent; referenced
from `docs/experiment_protocol_repair_liftability.md`).
