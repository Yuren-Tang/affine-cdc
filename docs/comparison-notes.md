# 對照筆記:OpenAI 原證明 / 原 Lean 庫 ↔ 本項目

用途:comparison layer 的地基;論文「等價重構與結構強化」論證的證據帳。
建立:2026-07-12(取得三份原始材料當日)。

## 原始材料(sources/,不入 git)

| 材料 | 位置 | 指紋 |
|---|---|---|
| 證明 PDF(3 頁) | `sources/cdc_proof.pdf` | sha256 `b4797f50…60fc13` |
| Prompt PDF(2 頁) | `sources/cdc_prompt.pdf` | sha256 `0e48deee…b758f3` |
| Lean 庫 | `sources/cdc-lean/`(github.com/openai/cdc-lean) | commit `577e9d9e…` |

cdc-lean:lean-toolchain **v4.31.0(與我們相同)**;Mathlib pin
`9a9483a92959bc92bd6a60176dd1fe597298c1f8`(**與我們的 v4.31.0 tag =
`fabf563…` 不同**——comparison layer 需先統一 pin 或做雙 pin 構建)。
共 16 檔、7134 行;審計方式:`Audit.lean` 印公理 + `rg` 掃 `sorry/axiom/native_decide`
(聲稱只餘三標準公理——與我們的驗證記錄同標準,建議我們也加 `Audit.lean`)。

## 原文結構(cdc_proof.pdf 實讀確認)

Lemma 2.1(二元素集族 ⟹ CDC,經 M_s 分解)→ 局部構造((2):排序 a,b,c,
`g_{v,a}=0, g_{v,b}=x, g_{v,c}=0`)→ 相容方程 (4) `t_u+t_v+ε_e f(e) = d_e`
(Lemma 2.2)→ 對偶化 (5)–(6) → λ 的奇偶詮釋 (9) → 每邊雙端計數收束。
引文中已含 Bermond–Jackson–Jaeger 一脈(8-flow、circuit 4-cover)之外圍
([1],[3]–[5],[7]–[9]),但未把 (2)–(9) 的機制與既有 Fano-flow 前史逐點定位
——正是 Bloom 批評與我們「考古」的切入點。

## 核心對應表(原 Lean ↔ 本項目)

| cdc-lean(CubicLabeling.lean 等) | 性質 | 本項目 | 性質 |
|---|---|---|---|
| `pairIndicator p h s : F₂`(if-then-else 指示) | 集合以指示函數表示 | `lineMk h s = P h`(陪集成員) | 商空間原語 |
| `local_pair_parity`:∀ x y t s,…(**decide,8⁴=4096 情形**) | 驗證一個解 | `isEven_localFamily` + **`localEquiv`(T1)** | 結構證明;分類**全部**解;任意 Γ |
| `pairIndicator_eq_of_difference`(**decide**) | 二點集相等判準 | `lineMk_eq_iff`、`coset_eq_pair`(B1) | 陪集相等,一行商論證 |
| `localBase G f v e := if e = edgeAt v 1 then f(edgeAt v 0) else 0` | **依賴頂點槽位排序** | 刪去點 `m_v` + `IsPlane.kappa`(選擇無關:`kappa_eq`) | 座標自由 |
| `compatibilityRhs` = `d_e` | 排序依賴的 RHS | `c_f(e) = κ_{u,e}+κ_{v,e}`(T3 B4 介面,T4 落地) | 天然類 |
| `compatibilityMap : (V→Γ)×(E→F₂) →ₗ (E→Γ)`(`ε` 槽) | 提升後的線性系統 | `δ_f : Γ^V → ⊕_e Q_e`(`ε` 由 B2 泛性吸收) | 商值系統 |
| `coordinateFunctional` + 對偶分離 | 原文 (5)–(9) | T5–T7(K(W)、β、唯一不變量、分支恆等式) | 待做 |
| 圖論底座(Expansion/JaegerKilpatrick/CubicTheorem/…) | 8-flow、化約 | **不重做**;comparison layer 直接接 | — |

## 對論文的三個直接後果

1. **「分類 vs 驗證」**:原庫以 4096 情形 `decide` 驗證特定構造的局部偶性;
   T1 證明局部解**恰為** `Γ`(自然 torsor),故原構造之「恰好可行」不是巧合而是
   分類的一個點。這是「結構強化」主張的最硬證據。
2. **座標帳目落實**:`localBase` 的 `if e = edgeAt v 1` 是 gauge 選擇的字面形式;
   `ε_e` 是 B2 商等式的提升變數;兩者在我們的鏈條中都被證明可消去。
   (ledger「原稿對象分類表」現在可對每項給出源碼行號級的引用。)
3. **一般性分界**:原文與原庫全程 `Γ = F₂³`;我們 T1–T5 在任意 F₂-向量空間成立,
   `dim Γ = 3` 只在 T6(Aut(Γ,W) 不變量唯一性)與 flow 存在性進場。

## Prompt(cdc_prompt.pdf 實讀確認)

任務陳述含「Assume for purposes of this task that a complete affirmative
proof exists」、только完整肯定證明可返回、≥8 小時、64 並行 agent 的
multiagent v2 策略、對抗審計清單(exact-two、平行邊 2-cycle、橋、循環化約)。
與對話紀錄的轉述一致;論文方法論一節可據此準確引述。
