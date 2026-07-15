# AffineCDC

**目前狀態（2026-07-15）**：本庫是 AffineCDC 的公開 Lean 審計與文件入口。現行狀態以本文件及 [`docs/00_READ_FIRST_ARCHITECTURE_CORRECTION.md`](docs/00_READ_FIRST_ARCHITECTURE_CORRECTION.md) 為準；其他舊導航、帳本及施工計畫如與二者衝突，均僅作歷史記錄。

## 核准的數學目標

> 每個有限無橋多重圖都有循環雙覆蓋。

此處允許自環。自然的循環物件是非空、按包含關係極小的 cut-even 邊集，因此單個自環本身即為一個 circuit。自然的有限性條件是有效邊集 `E(G).Finite`，不是整個 ambient vertex/edge type 有限。

作者已核准 **Path A**：日後把公開 Lean statement 乾淨遷移到上述完整命題及語義。此遷移**尚未實作**；本輪僅同步文件，不改任何 `.lean` 檔。

## 目前已由 Lean 核驗

現有公開 Lean 開發已包含：

- 局部 affine-family 分類及 quotient／gauge／dual／branching／Fano 核心；
- rank-three affine compatibility 的現行 branching/cross-bit 證明；
- indexed dart-support 構造及每邊恰覆蓋兩次的性質；
- 對一個已是 loopless cubic 且帶所需 nowhere-zero `F₂³`-flow 的圖，推出 CDC 的 `cubic_flow_cdc` corollary；
- 現行有限偶邊集的 circuit decomposition 工具。

上述成果均是真實的 checked Lean 結果，但**不等於**完整無條件定理已經 machine-checked。

## 尚未由 Lean 完成

- Path A 的公開 statement 遷移；
- 以 active edge-set finiteness 取代 ambient finiteness；
- cut-even circuit 語義與自環刪除／回插；
- graph-level multiset even double cover 作為獨立工程節點；
- cubic expansion、rank-three flow 與 collapse 的完整外層；
- pure cut-even collapse transport；
- 原 loopless core 上的一次最終 circuit decomposition；
- 完整有限無橋多重圖 CDC 定理。

現行 `lean/AffineCDC/Statement.lean` 仍是 **loopless、ambient-finite、尚未被證明的 implementation checkpoint**。它不是已核准的最終自然陳述，也不得被描述成已完成遷移。

## 核准的完整證明主幹

```text
有限無橋多重圖
→ 刪除自環
→ loopless 無橋核心
→ cubic expansion 與 rank-three flow
→ affine incidence compatibility
→ graph-level multiset even double cover
→ loopless 圖上的 vertex-even / cut-even 橋
→ pure cut-even collapse transport
→ 原 loopless 核心的 even double cover
→ 僅在此處作一次有限 circuit decomposition
→ 每個已刪自環加入兩個 singleton circuit occurrences
→ 完整有限無橋多重圖 CDC。
```

`cubic_flow_cdc` 是可保留、可審計的直接 corollary，但不是上述主幹的必要 waist，也不是公開最終定理。

## 獨立性

AffineCDC 的數學與 Lean 核心由本項目自己的分類、相容性及 cover 構造控制。其他 CDC formalization 不控制本項目的 theorem statement、圖編碼、工程架構或最終 proof path；本項目不得以直接調用另一套完整 CDC endpoint 代替自己的證明鏈。

## 構建與核驗

```bash
cd lean
lake exe cache get
lake build
lake env lean AffineCDC/Audit.lean
```

源碼掃描（預期無輸出）：

```bash
grep -rnE '\bsorry\b|\bnative_decide\b|^\s*(axiom|opaque|unsafe)\b' \
  lean/AffineCDC --include='*.lean' | grep -v Audit
```

## 文件優先序

1. 本 `README.md`；
2. [`docs/00_READ_FIRST_ARCHITECTURE_CORRECTION.md`](docs/00_READ_FIRST_ARCHITECTURE_CORRECTION.md)；
3. 實際 `.lean` 原始碼，用以確認目前已實作的精確狀態；
4. 其他已明標為歷史／superseded 的文件，僅供追溯。

歷史文件不得推翻目前入口，也不得把過去的 loopless endpoint、ambient-finite convention、可選整合或 `cubic_flow_cdc` 主線定位重新當成現行指令。
