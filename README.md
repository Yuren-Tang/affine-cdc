# AffineCDC — 對 OpenAI CDC 證明的數學考古

**目標**：對 OpenAI 2026-07-10 發表的 Cycle Double Cover 三頁證明做「規範不變化」的逆向工程（gauge-fixing 的反向操作）——剝除所有依賴局部座標、排序、任選基點的描述，只留下規範不變的數學本體，最終形成一篇關於**結構提純**的論文，並附帶完整的 Lean 形式化。

本項目**內容上獨立**於本工作區的 Erdős 306 項目，僅共享基礎設施（Lean 工具鏈 v4.31.0 + Mathlib 構建緩存，經 APFS clonefile 秒級複製，零額外磁盤）。

## 源頭

- 全程規劃討論：[docs/ChatGPT對話紀錄.md](docs/ChatGPT對話紀錄.md)（原鏈接 chatgpt.com/share/6a53dc5b-…）
- 核心重構：CDC 證明的真正主定理是 **Fano 相容性定理** —— 對三次圖上任意 nowhere-zero F₂³-flow，天然相容性類 `c_f ∈ ⊕ₑ Q_e`（`Q_e = Γ/⟨f(e)⟩`）落在 `im δ_f` 中；CDC 是其推論。
- 一切結構最終落回 **characteristic 2**：局部資料 = 規範場，頂點平移 = 規範變換，`[c_f] ∈ coker δ_f` = 規範不變量。

## 工作方式（三步節奏）

1. **紙面封閉**：精確定理、最弱假設、完整證明 → 記入 [docs/ledger.md](docs/ledger.md)（定理帳本）。
2. **Lean 薄驗證**：只形式化該塊核心定義與最重要定理；發現規格問題立即回修紙面。
3. **API 凍結**：塊不再變動後，才允許下一層依賴。

Lean 永遠落後紙面**一個模組**。

**本項目的 Lean 紀律**（用戶指令，優先於工程便利）：即便接受工程上的穩健措施，最終形態必須像數學一樣明徹——不犧牲一般性（任意 F₂-向量空間、不排序方向集）、不用 `sorry`、不以 tactic 堆砌掩蓋定義缺陷。若某塊在 Lean 中寫得扭曲，先懷疑定義，回修紙面。

## 目錄

```
AffineCDC/
  README.md            本文件
  docs/
    ChatGPT對話紀錄.md   源頭討論全文（用戶手動導出）
    ledger.md           定理帳本：每塊的精確陳述、狀態、Lean 對應
  lean/                 獨立 Lake 項目（只依賴 Mathlib）
    AffineCDC/
      Basic.lean              特徵二算術、方向、IsPlane（平面的內在 Klein 結構）
      Rank.lean               finrank = 2 → IsPlane 橋接（座標被隔離在此檔）
      LocalEvenFamily.lean    線族、覆蓋、偶性、平移作用
      LocalClassification.lean 定理 A：Γ ≃ LocalEvenFamily W + torsor 等變性
      Naturality.lean         推論 A2：沿線性同構的全套傳輸與交換圖
      Torsor.lean             推論 A1 打包：AddTorsor + 仿射同構
      OppositeFiber.lean      推論 A3：coset = 二點集、對向纖維刻畫
      EdgeQuotient.lean       T3：邊商泛性、κ 唯一性、標籤公式
      Gauge.lean              T4：coker 規範分類 + 對偶判準（任意域）
      DualConfig.lean         T5：K(W) 與交叉配對位元 β
      Invariance.lean         T6：β 的剪切唯一性（任意 Γ）
      Branching.lean          T7 F1：分支恆等式（dim 3 唯一進場處）
      Dart.lean               T7 F0：dart 圖層（規範自由的三次結構）
      Fano.lean               T7 F2/F3：Fano 相容性定理（庫終點）
      Comparison.lean         內化引理：原稿槽位構造 = Φ(t + f(b))
      Audit.lean              一鍵公理審計
```

## 構建與驗證

```bash
cd lean
lake exe cache get   # 取 Mathlib 緩存(或由同 rev 項目 clonefile)
lake build           # 全庫構建
lake env lean AffineCDC/Audit.lean   # 一鍵公理審計:T1–T7 應全為 [propext, Classical.choice, Quot.sound]
```

源碼掃描(應無輸出):
`grep -rnE '\bsorry\b|\bnative_decide\b|^\s*(axiom|opaque|unsafe)\b' lean/AffineCDC --include='*.lean' | grep -v Audit`

## 當前狀態

**七條定理規格全部封閉且 Lean 完成**(2026-07-13):T1 局部分類、T2 自然性/torsor、
T3 邊商泛性、T4 coker 規範分類、T5 交叉配對位元、T6 不變泛函唯一性(任意 Γ)、
T7 分支恆等式與全局消失。庫終點 = **Fano 相容性定理**
`DartFlow.exists_gluing`(`[c_f] = 0`)+ F3 標籤黏合;`dim Γ = 3` 唯一進場處
= `annihilator_unique`(codim-1 形式)。本庫完全自圓,不依賴外部證明代碼;
與原證明的逐項對應見 [docs/comparison-notes.md](docs/comparison-notes.md),
其槽位構造被內化為 `slotFamily_eq_localFamily`(字典 `m⁰ = t + f(b)`)。
實時帳本:[docs/ledger.md](docs/ledger.md)。下一階段:凍結期打磨
(import 精簡、真依賴審查、上游化審計)與論文寫作。
