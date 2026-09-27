# 対訳表(G4凍結版)— 内部語彙 → 論文語彙

原則: 論文本文・定理・図表は右列のみ。左列(内部語彙)はLean識別子とartifact内パス/JSONフィールドにのみ残置可(README_REPRODUCE.mdで「内部コードネーム」と注記済み)。

| 内部語彙 | 論文語彙 | 備考 |
|---|---|---|
| Sen24 / Sen24 base case | the base case of Sen's Paretian-liberal impossibility (two individuals, four alternatives) / the Sen instance | 初出でフル、以後 "the Sen instance" |
| lever | **constraint module**(短縮: module) | Lean型 `Lever` は§7と対応表でのみ言及 |
| minlib(bundled) | the bundled minimal-liberalism module $\mathsf{ML}$ | |
| decisive_voter0 / decisive_voter1 | the per-individual decisiveness modules $D_0, D_1$ | |
| asymm / un / no_cycle4 | asymmetry $\mathsf{A}$ / unanimity (weak Pareto) $\mathsf{U}$ / the local 4-cycle prohibition $\mathsf{C}_4$ | ロック済境界: full acyclicityと主張しない。"restricted local-rationality family"を明記 |
| Candidate B | the bundled/split realization pair | 本文で"Candidate B"禁止 |
| M1.5 | the non-canonicity theorem (Thm. 3.1) | 本文でM番号禁止 |
| M3-A / M3-B / M3-C | Thm. 5.1 / Thm. 5.2 / Thm. 5.4(iff = Thm. 5.5) | |
| raw repair | implementation-level (raw) minimal repair | "raw"は形容詞として残置可(grouped対比で標準的) |
| grouped repair | grouped repair | Leanと同一 |
| contract repair | contract-level repair | |
| groupTouchAny | the touched-atom map $\tau$ | |
| atom(契約側単位) | contract atom | |
| ≡CM | clause-multiset equivalence $\equiv_{\mathsf{CM}}$ **under the identity variable map** | G1で強化された表現に統一 |
| repair family | minimal-repair family | |
| atlas | case atlas | 付録のみ |
| 壁打ち/副査/β-discipline/主査 | (論文に出さない) | |
| encoding "sen24" | (artifact内のみ) | |

英語スタイル規約: 米式綴り、定理環境はamsthm経由のacmart既定、集合差は $\setminus$、Lean対応は付録Aの対応表で一元管理。
