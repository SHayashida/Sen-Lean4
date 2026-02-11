# Zenodo向け主張の骨子（保証範囲）

このアーカイブは、Senの不可能性定理の**固定ベースケース**（`n=2`, `m=4`）について、
Lean 4 と LRAT 検証により再現可能な検証結果を提供する。

## 1. 本アーカイブが保証すること

1. Lean定理としての不可能性（ベースケース）
   - `SocialChoiceAtlas/Sen/BaseCase24/Theorem.lean` の
     `sen_impossibility_basecase` により、`UN` と `MINLIB` が同時に成り立つと
     `SocialAcyclic` が成り立たないことを示す（ベースケース）。
2. SAT証明書のLeanカーネル検証
   - `SocialChoiceAtlas/Sen/BaseCase24/SATSenCNF.lean` の `lrat_proof` により、
     `Certificates/sen24.cnf` と `Certificates/sen24.lrat` の組を Lean 側で検証し、
     CNF が UNSAT であることを証明する。
3. CNF生成物の機械監査
   - `scripts/check_sen24_cnf.py` が、変数番号体系・節カテゴリ・節数・Manifest整合性を監査し、
     エンコード仕様への一致を機械的に検査する。

## 2. 本アーカイブが保証しないこと

1. 一般ケース（任意の `n`, `m`）の証明
   - 本成果は `n=2`, `m=4` のみを対象とする。
2. モデル外の公理系・定義への自動拡張
   - 現在の定義（`UN`, `MINLIB`, `SocialAcyclic` など）から外れる仕様の正しさは含まない。
3. SATソルバ自体の完全性証明
   - 必要なのは LRAT 出力であり、最終的な受理は Lean カーネル側検証結果に依存する。
4. 性能主張
   - 実行時間・メモリ・スケーラビリティに関する一般的保証は行わない。

## 3. 再現に必要な最小手順

1. `lake build`
2. `python3 scripts/gen_sen24_dimacs.py`
3. `python3 scripts/check_sen24_cnf.py Certificates/sen24.cnf --manifest Certificates/sen24.manifest.json`
4. `cadical --lrat --no-binary Certificates/sen24.cnf Certificates/sen24.lrat`
5. `lake build SocialChoiceAtlas.Sen.BaseCase24.SATSenCNF`

## 4. 追跡可能性（artifact traceability）

- Pure Lean proof:
  - `SocialChoiceAtlas/Sen/BaseCase24/Theorem.lean`
- SAT+LRAT verification in Lean:
  - `SocialChoiceAtlas/Sen/BaseCase24/SATSenCNF.lean`
  - `Certificates/sen24.cnf`
  - `Certificates/sen24.lrat`
- CNF spec/audit:
  - `scripts/gen_sen24_dimacs.py`
  - `scripts/check_sen24_cnf.py`
  - `Certificates/sen24.manifest.json`
  - `Certificates/CNF_AUDIT.md`

