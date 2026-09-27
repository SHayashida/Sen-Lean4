# M3先行研究調査後の研究差分メモ — repair correctness と reporting correctness の境界

宛先: 石川冬樹先生
日付: 2026-09-27

## 1. 先生からの懸念

今回の先行研究調査で出発点とした懸念は、抽象化、lifting、診断、最小修復にはすでに厚い蓄積があり、M3が「抽象化によって修復集合が変わり得る」「射影によって最小性が変わる」と述べるだけでは研究差分にならない、という点です。この懸念は妥当でした。したがって現在の原稿は、抽象化一般、最小集合計算、修復の射影、射影後の再最小化を新規性として主張しません。

## 2. 調査で既知と確認したもの

調査対象では、次の要素は既知の基盤または強い隣接研究として扱うべきだと確認しました。

- 階層的・構造的な抽象化と粗粒度の診断表現
- 修復・診断結果のliftingと表現間の対応
- 低水準解を得た後のpost-hoc projection
- 射影後のre-minimizationと最小集合の変化
- 抽象化のsoundness/completeness条件
- MUS/MCS等を含むminimal-set machinery
- 証明証明書、検査器、独立再検査という一般的な保証構造

特に Grastien et al. (2023) は、post-hoc projectionとprojection/re-minimizationに関する強い先行研究です。そのためM3は、射影という機構や、射影が最小修復族を変えるという事実自体を新規性に含めません。一方、Autio & Reiterについては原典未確認の軸があり、二次資料だけから無条件の不在主張を行いません。調査結果は7文献×8軸の比較表に固定しましたが、これは文献世界全体に対する不在証明ではありません。

## 3. 現在残っているM3の中心差分

現在の研究質問は次のように狭めています。

> When may verified low-level repairs be reinterpreted under an independently specified reporting semantics?

M3では、実装側の充足述語 `SatPhi` と報告契約側の充足述語 `SatPsi` を独立した引数として与えます。`SatPsi` は `SatPhi` とgroupingから定義的に生成されません。ただし、両者を無関係な任意の意味論として置いているわけでもありません。block-alignedな残余集合について両者を結ぶ明示的な橋が `ResidualFaithfulness` です。

この構成により、低水準で計算・検証された修復が正しいという **repair correctness** と、その修復を別途定めた報告意味論の下で再解釈してよいという **reporting correctness** を分離します。現在確認した主要先行研究の範囲では、同じ保証境界を独立したreporting contractとして定式化したものは確認していません。ただし、これは新規性が証明されたという意味ではなく、調査済み範囲での限定的な位置づけです。

## 4. 現在証明済みの結果

現在の主張はLeanで確認済みの範囲に限定します。

M3-Bは、atomicityや単調性を仮定せず、次を示します。

```text
BlocksDisjoint
+ ResidualFaithfulness
+ GroupSoundness
=>
GroupedRepair = ContractRepair
```

M3-Cでは、`BlocksDisjoint` と `ResidualFaithfulness` に加えて、target-sideの `PsiDeletionMonotonicity` を仮定すると、次のexactnessが得られます。

```text
GroupSoundness
<->
GroupedRepair = ContractRepair
```

ここでconverse theorem `m3c_converse` 自体は `ResidualFaithfulness` を仮定しません。また `audit_cost_collapse` は、target-side deletion monotonicityの下で、無制限の `GroupSoundness` 確認をraw minimal repairs上の確認へ縮約します。この有限降下には `SatPhi` のdeletion monotonicityを仮定していません。

## 5. 事前アトミック化への現在の回答

Atomicityは強い十分条件であり、事前にrepair atomを適切に細分化できれば、表現損失の一部を回避できます。したがってM3は、pre-atomicizationが無効であるとも、常にpost-hoc reportingが必要であるとも主張しません。

しかしatomicityを採用しても、実装修復の正しさと、独立に指定されたtarget reporting semanticsの下でその修復をどう報告してよいかという概念上の区別は残ります。また現在のM3-Bは、atomicityが成立しない場合でも `GroupSoundness` が成立するregimeを扱います。従って現在の論点は「atomicityか否か」ではなく、どの明示的な意味論的義務がreporting correctnessを正当化するかです。

## 6. 今後の博士研究候補

次はすべて **現在は未証明** であり、現論文の成立条件ではありません。

1. `GC <-> FS ∧ CRLift` のようなfrontier-obligation factorization
2. atomicityより弱いpre-group/post-hoc equivalence条件
3. repair frontierが不完全な場合のassurance degradation
4. reporting-aware certificate contracts

これらは、現在の定理を完成させるための残作業ではなく、独立した博士研究候補です。特にfactorizationは、frontier equalityを直接検査するよりも運用上安価または監査しやすい場合にのみ追究する価値があります。

## 7. 現在の判断

当初の広い新規性主張は、先行研究調査によって明確に狭まりました。一方、現在のM3は、verified low-level repairと独立指定されたreporting semanticsの間の保証境界を、`ResidualFaithfulness`、`GroupSoundness`、target-side monotonicityによって分離する形で残っています。これは調査後の方が防御可能な研究差分です。

現時点で必要なのは、新しい例や定理を追加することではありません。次の戦略判断は、現在のM1.5+M3単位を博士研究の公表時期まで保持するか、現行の狭いclaim boundaryのまま投稿準備へ移すかです。
