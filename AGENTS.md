# AGENTS.md
# SocialChoiceAtlas / Possibility Atlas — Agent Guide

## 0. Mission (North Star)
This repository turns social choice impossibility results into an **engineering-grade search problem**:
we treat axioms as **levers** (ON/OFF/relaxation) and study what separates **SAT vs UNSAT** under a small scope,
to build a **Possibility Atlas** (a map of “where feasibility breaks” and “how to repair it”).

- **Search** runs on fast engines (SAT / OMT / optimization).
- **Check** is guaranteed by the **Lean kernel** (proof-carrying when possible).
- Deliverables are a **reproducible search+verification pipeline** and **insights based on boundary identification (MUS/MCS)**.

### 0.1 Language Policy (Hard Rule)
**All agent outputs, docs, logs, and PR text MUST be in English.**
- Exception: quoting existing artifacts or external text verbatim.
- If the user requests Japanese explicitly, comply for that output only.

### 0.2 Public Repository Safety (Hard Rule)
`AGENTS.md` is a committed public file. Keep it free of:
- secrets or credentials,
- internal-only infrastructure details,
- private/local absolute paths.

Use repository-relative paths and generic tooling instructions only.

## 1. Current Status (What exists)
The repo already contains a working, audited pipeline around the Sen “Liberal Paradox” base case (n=2, m=4), plus atlas tooling.
At minimum, these exist and must remain stable:

- Formalization in Lean, plus CNF (DIMACS) + LRAT verification in Lean.
- Generator + auditor for the committed baseline:
  - `scripts/gen_sen24_dimacs.py` (compat wrapper)
  - `scripts/gen_dimacs.py` (leverized generator)
  - `scripts/check_sen24_cnf.py` (baseline / sen24-family auditor)
  - `Certificates/sen24.cnf`, `Certificates/sen24.manifest.json`, `Certificates/sen24.lrat`
- Atlas tooling (sen24-fixed):
  - `scripts/run_atlas.py` (enumeration + solver execution + proof metadata)
  - `scripts/mus_mcs.py` (MUS/MCS extraction for UNSAT solved cases)
  - `scripts/decode_model.py` (human-readable rule + triviality scores)
  - `scripts/summarize_atlas.py` (atlas_summary output)

## 2. Core Claim (Paper-level)
We provide a framework to run **engineering-relevant “breakthrough feasibility exploration”**
as a **search problem over axiom levers**.

- The goal is **not** to re-prove a general theorem for arbitrary n,m.
- The goal is to **systematically explore design space** where contradictions disappear,
  using **SAT + proof logs + Lean verification**.
- The goal is not “enumerating all subsets”, but **identifying the feasibility frontier** and **extracting repair levers**.

## 3. Non-goals (Anti-goals)
- Claiming an “all-n,m scalable universal atlas” from day 1 (combinatorial explosion will kill it).
- Claiming we replace MAXSAT/OMT/PB solvers (premature; differentiation must be precise).
- Exhaustive philosophical coverage of social choice (stay engineering-focused).

## 4. Design Principles (Hard Constraints)

### 4.1 Killable Problem First
Start with a **small but fully solvable** instance, and demonstrate value there.

- Example: for n=2, m=4, explore ~5–8 axiom levers and generate an atlas.
- Explicitly adopt the **Small Scope Hypothesis**: the “kernel” of many impossibilities is often local (cycles, etc.).
- **Defense (for papers):** MUS/frontier identified in minimal cases offers heuristic insight for larger cases.
  It is **not** a substitute for a general theorem.

### 4.2 Separation of Concerns: Spec / Encode / Solve / Check
- **Spec:** axioms as human-readable specifications (Lean/Markdown).
- **Encode:** transform to CNF/SMT (Python).
- **Solve:** SAT/OMT/optimization (external solvers).
- **Check:** verify artifacts (CNF, proof logs) by the Lean kernel.

### 4.3 Everything is Auditable
- Generators must emit a **manifest** (variable domains, clause counts, per-category counts, hashes).
- Auditors must be able to prove “conforms to spec” mechanically.
- Preserve proof logs (LRAT/DRAT) and verify in Lean (do **not** trust solver outputs blindly).
- “Smart search” (symmetry reduction, pruning) may be heuristic in Python; **final correctness is proof+Lean**.

## 5. Research Questions (Next-phase)
RQ1: Which axiom sets form the SAT/UNSAT **frontier**?  
RQ2: What are minimal UNSAT causes (MUS/SMUS)? Which levers matter most?  
RQ3: What is the minimal repair (MCS / minimal relaxation set) to restore SAT?  
RQ4: With graded weakening parameters, how does the frontier move continuously?  
RQ5: How does this relate to Constraint Hierarchies / ATMS / OMT / MAXSAT, and what is the novelty?

## 6. Differentiation Targets (Must be addressed)
Implementation must be accompanied by “Related Work” positioning.

- **Constraint Hierarchies:** resolve conflicts via prioritized constraints; here we **map the SAT/UNSAT structure itself**
  and identify cause+repair via **MUS/MCS**.
- **ATMS:** manages consistency of assumption sets; close in spirit, but we add:
  1) **CNF + proof logs + Lean** for auditable verification,
  2) a path to **parametric weakening** (continuous levers),
  3) **human-readable rule extraction** as a first-class output.
- **OMT / MAXSAT / PB:** primarily optimization-driven.
  Our first deliverable is **(a) atlas generation** and **(b) MUS/MCS cause+repair identification**,
  and only later (optionally) connect to optimization as “minimum relaxation”.
- Avoid “speed competition”: emphasize **auditable proofs (LRAT, etc.) + Lean verification**.

## 7. Engineering Application Story (Concrete)
“Engineering feasibility exploration” must be grounded in at least one concrete case before expanding:

Priority:
1) **Voting rule design (new implementable mechanisms):** enumerate SAT rules under relaxed axioms and explain them via MUS/MCS.
2) **AI-assisted social choice computation:** integrate search → verification → explanation (auditable governance).
3) Later: resource allocation / safety constraints only after (1) is demonstrated.

## 8. Implementation Roadmap (Agent must follow)

### Phase 1: Leverization
- Factor axioms as modules (`encoding/axioms/*.py`).
- CLI to select axiom levers (example uses current sen24 naming):
  `python3 scripts/gen_dimacs.py --n 2 --m 4 --axioms asymm,un,minlib,no_cycle3,no_cycle4`
- Always output:
  - CNF (DIMACS)
  - manifest.json (hash + per-category counts)
  - (optional) solver outputs (SAT model / UNSAT proof log)

Definition of Done:
- The committed Sen24 UNSAT baseline reproduces, and Lean verification passes.
- A relaxed case (e.g., removing `minlib`) becomes SAT and yields a human-readable rule.

### Phase 2: Atlas Generation (Frontier + extraction + visualization)
Phase 2 is not “brute force only”; it must include boundary intelligence.

MUST:
1) **Frontier identification**
   - For each UNSAT solved case: extract MUS/SMUS (cause levers)
   - If possible: extract **MCS** (repair levers: minimum to relax to restore SAT)
2) **Search-space reduction**
   - Symmetry reduction (heuristic is fine in Python)
   - Monotone/implication pruning where valid
   - Incremental SAT (assumptions) to maximize reuse
3) **Human-readable rule extraction (mandatory)**
   - Convert SAT models (bitstrings) into readable representations and save them:
     - minimum: lookup table / preference comparison matrix
     - recommended: decision trees or simple if-then rules (not necessarily optimal)
   - Aim for paper-quality figures.

Deliverables:
- SAT/UNSAT per axiom subset
- MUS (and preferably MCS) for UNSAT
- Representative non-trivial SAT rules (with triviality scores)
- JSON/CSV + visualization (Hasse diagram / heatmap)

### Phase 3: Scalability Story (Answer the complexity wall)
- Show why it blows up (math + measurements vs n,m,#axioms).
- Offer **search strategies** (not “full generalization”):
  - incremental SAT (assumptions)
  - symmetry breaking / reduction
  - monotone/implication pruning
  - caching MUS/SMUS/MCS
- Position vs MAXSAT/OMT by “how to achieve the same goal”, and clarify our axis:
  **Atlas + MUS/MCS + Lean-audited artifacts**

## 9. Repo Rules (Non-negotiable)
- Every generated artifact must be hash-tracked; reproduction steps must be recorded in README(s).
- Auditors must reconstruct expectations **independently** from the generator.
- Lean should not directly import huge generated formulas; keep CNF+include_str+LRAT approach.
- `Certificates/atlas/` should commit at most **one fixed proof-carrying case** (currently `case_11111`);
  all other cases must be regenerated under `results/...` or `/tmp` and tracked by hashes.
- On any change, the following must pass:
  - CNF regeneration
  - strict auditing against manifest
  - Lean builds for baseline and committed proof case
  - (if available) solver proof regeneration (e.g., `cadical --lrat ...`)

### 9.1 Baseline Protection (Hard Rule)
Do not modify committed baseline artifacts unless explicitly requested and justified:
- `Certificates/sen24.cnf`
- `Certificates/sen24.manifest.json`
- `Certificates/atlas/case_11111/**`

## 10. Agent Workflow (How to act)
1) Classify requests as **Spec change** vs **Implementation change**; update spec first.
2) Update in order: generator → manifest → auditor → Lean verification.
3) Every new axiom lever must be validated on a minimal example (SAT/UNSAT behavior).
4) Atlas runs must include MUS/MCS and rule extraction in one coherent pipeline.
5) Any research-positioning change must be captured in `docs/` notes immediately.

## 11. Output Formats (Standard)
- One case directory: `results/<date>/<case_id>/` (or `/tmp/...` for local runs)
  - `sen24.cnf`
  - `sen24.manifest.json`
  - `solver.log`
  - `model.json` (SAT) **or** `proof.lrat` (UNSAT)
  - `summary.json` (required; includes reproducibility fields and solver metadata)
  - `mus.json` (required for UNSAT solved cases)
  - `mcs.json` (recommended where feasible)
  - `rule.md` / `rule.json` / `rule.dot` (required for SAT cases)
- Atlas directory: `results/<date>/`
  - `atlas.json` (top-level summary + cases)
  - `atlas_summary.md`
  - `atlas.svg/png` (optional visualization)

## 12. Definition Discipline
- Universal Domain (Unrestricted Domain) must be explicit: either as a total function in Lean typing
  or as a theorem precondition guaranteeing no domain restriction.
- Keep order/structure assumptions minimal:
  - If acyclicity suffices, do not add transitivity/linear order.
  - If stronger structure is needed, document *why* in comments/spec.

## 13. Practical Risks & Guards (Must consider)

### 13.1 Trivial SAT solutions (dictatorship / constant functions)
SAT solvers often return trivial solutions. You MUST implement at least one:
- Filtering: detect and exclude dictatorship/constant/one-agent dominance.
- Objective: encourage non-triviality (later can connect to MAXSAT/OMT/PB).
- In papers: explicitly show “after excluding trivial solutions, we can extract interesting rules”.
- At minimum, emit light triviality scores (e.g., dictatorship score, constancy, neutrality deviations).

### 13.2 Complexity creep (over-implementation)
- Do not attempt to formally prove symmetry/pruning heuristics inside Lean at early stages.
- Keep symmetry reduction and pruning in Python; Lean is for verifying CNF+proof artifacts.

### 13.3 Safety specs for pruning/symmetry (must be documented)
When using monotone pruning or symmetry reduction, you MUST follow the repo’s safety specs:
- `docs/assumptions_monotone_pruning.md`
- `docs/safety_symmetry_reduction.md`

---

## CLAUDE.md compatibility
If your tooling reads `CLAUDE.md`, you may copy this file as-is to `CLAUDE.md`.
(Keeping content identical is recommended.)

## 14. Local Private Overrides (Not committed)
You may define local/private instructions in `AGENTS.local.md` (or `AGENTS_PRIVATE.md`) at repo root.
- These files are intentionally git-ignored and must never be committed.
- They may extend local workflow details, but must not weaken baseline protection, auditing, or CI requirements.
- If present, apply them after `AGENTS.md`.
