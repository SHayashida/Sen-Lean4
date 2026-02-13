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


<!-- # AGENTS.md
# SocialChoiceAtlas / Possibility Atlas — Agent Guide

## 0. Mission (North Star)
本リポジトリの目的は、社会選択・不可能性定理を「工学的に扱える探索問題」に落とし込み、
**公理（axioms）を“レバー”としてON/OFF/緩和したときに何がSAT/UNSATを分けるのか**を
小スコープで探索し、**突破可能性の地図（Possibility Atlas）**を構築することである。

- 探索（Search）は高速系（SAT/OMT/最適化）で回す
- 検証（Check）は Lean カーネルで担保する
- 成果物は「再現可能な探索・検証パイプライン」と「境界同定（MUS/MCS）に基づく洞察」

## 1. Current Status (What exists)
- Sen (n=2, m=4) base case の形式検証（Lean）と、CNF(DIMACS)+LRAT の Lean 検証がある
- `scripts/gen_sen24_dimacs.py` が `Certificates/sen24.cnf` を生成
- `Certificates/sen24.lrat` を Lean で検証し `sen24_cnf_unsat` を提供
- `scripts/check_sen24_cnf.py` と `Certificates/sen24.manifest.json` により「生成器が仕様どおり」を機械監査可能

## 2. Core Claim (Paper-level)
**工学的に重要な「突破可能性の探索」を、公理の“レバー”を変える探索問題として回せる枠組みを提供する。**
- “定理の一般証明”が主目的ではない
- “レバー操作により矛盾を回避する設計空間”を、SAT/証明ログ/Lean検証で厳密に探索する
- 目的は「全探索の列挙」ではなく、**矛盾境界（frontier）の同定**と**修復レバーの抽出**である

## 3. Non-goals (Anti-goals)
- いきなり一般 n,m でスケールする「万能アトラス」を作る（組合せ爆発で破綻する）
- 既存の最適化（MAXSAT/OMT/PB）を置き換える主張を先に立てる（差別化が未整備の段階では危険）
- “社会選択の哲学的議論”の網羅（工学的枠組みに集中）

## 4. Design Principles (Hard Constraints)
### 4.1 Killable Problem First
「小さくても完全に解ける」問題を最初に設定し、そこで手法の価値を示す。
- 例: n=2,m=4 の極小空間で、5〜8個程度の公理レバーを探索し Atlas を生成
- “Small Scope Hypothesis” を明示（核は小スコープに凝縮される、目的は競合関係の解明）
- **Defense（論文用）**: 不可能性の「核」は局所的構造（サイクル等）に起因しやすい。よって最小ケースで得られる
  MUS/境界は、一般ケースの主要な矛盾要因に対するヒューリスティックな示唆を与える（一般定理の代替ではない）。

### 4.2 Separation of Concerns: Spec / Encode / Solve / Check
- Spec: 公理を人間可読な仕様（Lean/Markdown）として定義
- Encode: CNF/SMT など solver 入力に変換（Python）
- Solve: SAT/OMT/最適化で探索（外部ソルバ）
- Check: 生成物（CNF, proof log）を Lean カーネルで検証し、再現性を確保

### 4.3 Everything is Auditable
- 生成スクリプトは manifest（変数域・節数・カテゴリ別カウント・ハッシュ）を必ず出す
- 監査スクリプトで「仕様どおり」を機械的に証明可能にする
- LRAT/DRAT 等の証明ログを保存し Lean 側で検証する（“solver を信頼しない”）
- 探索の賢さ（対称性削減等）は Python 側のヒューリスティックで良い。**最終正当性は証明書＋Lean**で担保する。

## 5. Research Questions (Next-phase)
RQ1: どの公理集合が SAT/UNSAT を分ける境界（frontier）を作るか？  
RQ2: UNSAT の最小原因（MUS/SMUS）は何か？ “レバー”として最重要なのはどれか？  
RQ3: **UNSAT を SAT に戻す最小修復（MCS / 最小緩和集合）は何か？**（突破レバー＝工学的操作量）  
RQ4: 公理緩和（弱化パラメータ）を導入すると frontier はどう連続的に動くか？  
RQ5: 既存枠組み（Constraint Hierarchies / ATMS / OMT / MAXSAT）と比較して、本枠組みの新規性は何か？  

## 6. Differentiation Targets (Must be addressed)
エージェントは実装だけでなく、論理武装（Related Work）の差別化要点も同時に整備すること。

- Constraint Hierarchies: “優先順位付き制約”で衝突解消するが、ここでは
  **「公理セットのSAT/UNSAT構造」自体を地図化**し、MUS/MCSで“衝突原因と修復”を同定する。
- ATMS: “仮定集合の整合性管理”だが、ここでは
  **社会選択公理を仮定として扱い、整合境界を探索**する点が近い。差分は
  1) CNF/証明ログ/Lean検証による“形式的監査可能性”
  2) 公理弱化パラメータ（連続レバー）まで含める設計余地
  3) ルール抽出（human-readable）を成果物に含める
- OMT / MAXSAT / PB: これらは“最適化”が主眼。
  本プロジェクトは **(a) Atlas生成（境界の可視化）** と **(b) MUS/MCSによる原因同定・修復同定**
  を第一成果に置く。必要なら後段で「最小緩和量」＝最適化へ接続する。
- MAXSAT等への接続は「速度競争」ではなく、**監査可能な証明書（LRAT等）＋Lean検証**を価値軸に置く。

## 7. Engineering Application Story (Concrete)
“工学的突破可能性”は、少なくとも以下の1つに具体化してから拡張する。
優先順位:
1) **投票規則設計（未実装の制度探索）**: 公理の緩和で実装可能な新ルールを列挙・検証し、MUS/MCSで説明可能にする
2) **AIによる社会的選択計算の基盤**: 探索→検証→説明（MUS/MCS）を組み込む（Auditable governance）
3) （将来）資源配分・安全性制約等への横展開は、上記ケーススタディ成立後

## 8. Implementation Roadmap (Agent must follow)
### Phase 1 (Immediate): Leverization (スイッチ化)
- 公理を“モジュール”として分離: `axioms/*.py` あるいは `encoding/axioms/*.py`
- CLIで公理集合を指定可能に:
  `python scripts/gen_dimacs.py --n 2 --m 4 --axioms Pareto,MinLib,NoCycle3,NoCycle4`
- 出力は常に:
  - CNF (DIMACS)
  - manifest.json（ハッシュとカテゴリ別カウント含む）
  - (任意) solver 結果（SATならモデル、UNSATなら証明ログ生成コマンド）

Doneの定義:
- “既存 Sen24 UNSAT” がこの新パイプラインで再現され、Lean で `lake build ...SATSenCNF` が通る
- “MinLib を外す”等の緩和ケースで SAT になり、モデルをデコードして**人間可読な例**を出せる

### Phase 2: Atlas Generation (境界探索＋抽出＋可視化)
Phase 2 は「単なる総当たり」ではなく、**境界同定の知的操作**を必須化する。

必須要件（MUST）:
1) **境界同定**:
   - 各UNSATケースで MUS/SMUS を抽出（原因レバー）
   - 可能なら **MCS（最小修復集合）** を抽出（突破レバー：最小で何を緩めればSATになるか）
2) **探索空間の縮約**:
   - 対称性（neutrality/匿名性等）を利用して探索空間を削減（実装はPython側ヒューリスティックでOK）
   - 含意・単調性に基づく pruning（例：公理追加でSAT→UNSAT方向にしか動かない場合の枝刈り）
   - インクリメンタルSAT（assumptions）で再利用を最大化
3) **Human-readable rule extraction（必須）**:
   - SATモデル（ビット列）を、人間可読な表現に変換して保存する
   - 最低限: ルックアップテーブル / 比較行列
   - 推奨: 単純な決定木（Decision Tree）や If-Then ルールへの蒸留（完全最適でなくて良い）
   - 論文図表（Figure）として提示できる形式を意識する

成果物:
- 公理部分集合ごとの SAT/UNSAT
- UNSAT なら MUS（+可能なら MCS）
- SAT なら human-readable ルール（trivial除去後の代表例）
- 結果を JSON/CSV に保存し、可視化（Hasse図/ヒートマップ）を生成

### Phase 3: Scalability Story (計算複雑性の壁への答え)
- 「なぜ爆発するか」を先に数式と実測で示す（n,m,axioms数に対する増大）
- 対策を **“探索戦略” として**提示（完全一般化ではなく、現実的な探索制御）
  - インクリメンタルSAT（assumptions）
  - 対称性破り（neutrality/匿名性などがある場合）
  - 事前 pruning（単調性・含意）
  - MUS/SMUS/MCSのキャッシュ
- 比較対象（MAXSAT/OMT）には “同じ目的を達成するにはどう使うか” を整理し、
  本枠組みの位置づけ（Atlas + MUS/MCS + Lean監査）を明確化

## 9. Repo Rules (Non-negotiable)
- 生成物にハッシュを付け、再現手順をREADME/Certificates/READMEに残す
- 監査スクリプトは **仕様（manifest）と独立**に期待値を再構築できること
- Lean 側は “重い生成済み式” を直接 import しない方針を維持（CNF+include_str+LRAT検証）
- `Certificates/atlas/` の固定コミットは原則1ケース（`case_11111`）に限定し、他ケースは `results/...` / `/tmp` で再生成してハッシュで追跡すること
- 変更時は必ず以下が通ること:
  - `python scripts/gen_*.py`（再生成）
  - `python scripts/check_*.py ... --manifest ...`
  - `lake build ...SATSenCNF`
  - （可能なら）`cadical --lrat ...` の再生成

## 10. Agent Workflow (How to act)
1) 変更要求を「Spec変更」か「実装変更」かに分類し、先に spec を更新
2) 生成器→manifest→監査器→Lean検証の順でアップデート
3) 新しい公理レバーは “最小例” でSAT/UNSATの挙動を必ず確認
4) Atlas実験では MUS だけでなく **MCS/ルール抽出**までを同一パイプラインで回す
5) 研究的主張（差別化/応用/スケール）に関わる点は、同時に `docs/` にメモを残す

## 11. Output Formats (Standard)
- 実験1ケース = `results/<date>/<axiom_set_id>/`
  - `cnf.dimacs`, `manifest.json`, `solver.log`,
  - `model.json`（SAT） or `proof.lrat`（UNSAT）,
  - `mus.json`（UNSAT必須）, `mcs.json`（可能なら）,
  - `rule.txt|rule.json|rule.dot`（SATの人間可読表現）,
  - `summary.md`
- Atlas = `results/<date>/atlas.json` + 可視化 `atlas.svg/png`

## 12. Definition Discipline
- Universal Domain (Unrestricted Domain) は “全域関数” として明示するか、
  あるいは前提に domain 制約が無いことを Lean の型で保証すること
- 社会的選好の公理は “必要最小限” を原則にする:
  - Acyclicity のみで済むなら Transitivity/Linear order を追加しない
  - 追加する場合は “なぜ必要か” をコメントで説明

## 13. Practical Risks & Guards (Must consider)
### 13.1 Trivial SAT solutions (独裁・定数関数) 問題
SATが返す解が「独裁」など自明になりがち。以下のいずれかを必ず実装する。
- フィルタリング: 独裁・定数・単一個人支配などを検出して除外
- 目的関数: “なるべく非自明”を誘導（後段でMAXSAT/OMT/PBに接続してもよい）
- 論文では「自明解を除いた上で、面白いルールを抽出できる」点を示す
- 少なくとも `decode_model` 等で軽量な自明解スコア（例: dictatorship score, constancy, neutrality偏差）を出力し、説明可能性を確保する

### 13.2 Complexity creep (実装過多) 問題
- 対称性利用の厳密証明を Lean 側で頑張りすぎない（泥沼化する）
- 対称性縮約・探索ヒューリスティックは Python に寄せ、Lean は検証（CNF+証明書）に徹する

---
## CLAUDE.md compatibility
Claude系ツールで `CLAUDE.md` を読む運用をする場合は、本ファイルを複製して使用してよい。
（内容は同一であることを推奨） -->
