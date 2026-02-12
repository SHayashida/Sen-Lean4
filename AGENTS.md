# AGENTS.md
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

### 13.2 Complexity creep (実装過多) 問題
- 対称性利用の厳密証明を Lean 側で頑張りすぎない（泥沼化する）
- 対称性縮約・探索ヒューリスティックは Python に寄せ、Lean は検証（CNF+証明書）に徹する

---
## CLAUDE.md compatibility
Claude系ツールで `CLAUDE.md` を読む運用をする場合は、本ファイルを複製して使用してよい。
（内容は同一であることを推奨）