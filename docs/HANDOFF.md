# 交接文件(Fable 5 → Opus 4.8,2026-07-13)

Fable 5 額度將盡。本文件讓接手模型無縫繼續。**先讀此文件 + `docs/ledger.md`
(定理帳本)+ `docs/架構圖.md`(真依賴圖)。** 用戶 = Yuren Tang(David),
全程中文交流,合作者關係(見記憶 [[affinecdc-collaborator-mandate]])。

## 項目一句話

對 OpenAI 的 CDC(Cycle Double Cover)三頁證明做「規範不變化」的結構提純:
七條定理(T1–T7)+ CDC 抽取(G),全部 Lean 形式化。**已全部完成、零 sorry、
公理標準、CI 綠、公開於 github.com/Yuren-Tang/affine-cdc。**

## 當前戰局(2026-07-13)

- **數學+Lean**:T1–T7 + G 雙側完成。17 檔,`import Mathlib` 二層策略。
- **基建**:GitHub public,`main`+`dev`,CI = 構建+公理審計+env-lint+源碼掃描。
  **Release 鐵律**:任何 tag/release 前完成狀態交用戶審查(Zenodo DOI 潔淨)。
- **工具審查**:shake(內部 import 已按真依賴精簡)、runLinter(全綠,入 CI)。

## 進行中任務:可獨立核驗的 CDC 端口(用戶本輪要求)

**目標**:讓圖論/外領域專家能在一個獨立 audit 裡快速確認「本文聲稱證明的
CDC 就是標準 CDC,無非-Mathlib 定義偷梁換柱」——不必深入我們的證明。
採 **FLT 的 Statement/Port 分離模式**(用戶已授權大膽適用)。

### 設計(Fable 5 已定,待實作)

1. **`AffineCDC/Statement.lean`** — **只 `import Mathlib`,零我們庫詞彙**。
   - 用 Mathlib 新的 `Graph α β` 多重圖 API(`Mathlib/Combinatorics/Graph/Basic.lean`,
     v4.31.0 已有;`IsLink`/`Inc` 容許平行邊——正是 CDC 所需;`SimpleGraph`
     不行,無平行邊)。
   - 「無橋」「循環」「循環雙覆蓋」的定義**就寫在此檔內**(Mathlib 尚無 cycle
     double cover;圖 API 也young)——保持極短可通讀(目標 ≤ 一屏)。
   - 最終陳述形如:`theorem cycle_double_cover (G : Graph α β) [Finite]
     (hbridgeless : …) : ∃ (cover : Multiset …), …`(每邊恰現兩次)。
   - **關鍵**:此檔不出現 `DartFlow`/`IsPlane`/`LineSpace`/`codim` 等——
     專家只讀此檔 + `#print axioms` 即可核驗定義忠實性。
2. **`AffineCDC/Port.lean`** — 橋接:從我方 `exists_cycle_double_cover`
   (dart 形式,`Cycle.lean`)推出 `Statement.lean` 的陳述。這裡承擔
   「dart 結構 ↔ Graph α β」「support/ρ-軌道 ↔ Multiset of cycles」的翻譯。
   *需要*:8-flow 存在性 + 三次化約——**這兩步引文獻,可在 Port 裡以假設
   (hypothesis)形式出現**,或若 Mathlib 有 8-flow 則接;否則陳述為
   「給定 nowhere-zero F₂³-flow 的條件 CDC」——與庫終點一致,誠實標註。
3. **`AffineCDC/AuditStatement.lean`** — 專供外部核驗:
   `#print axioms cycle_double_cover` + `#print` 陳述本身 + 列印所有
   Statement.lean 內的自定義 def。CI 加一步確認其只依賴標準三公理。

### 實作提示(Fable 5 偵察所得)

- `Graph α β`:`G.IsLink e x y`(邊 e 端點 x,y)、`G.Inc e x`、`E(G) : Set β`、
  `G.incidenceSet x`。先 `Read Mathlib/Combinatorics/Graph/Basic.lean` 全文。
- 「橋」= 刪之增連通分量;或用「無 nowhere-zero flow ⟺ 有橋」的等價繞開——
  但端口要**標準**定義,勿用 flow 定義橋(那是我們的路徑)。權衡見下。
- **建議先做最小可信版**:條件 CDC(給定 flow)先通,把 8-flow/化約作為
  顯式 hypothesis;再逐步接 Mathlib 現成定理。不要為完美卡住主交付。
- dart↔Graph 翻譯:我方 `Δ`=darts、`σ`=邊對合、`vtx`。Graph 的邊 `β` ↔
  `Δ/σ`;`IsLink e x y` ↔ 存在 dart d,`σ`-對 d/σd,`vtx d=x`,`vtx σd=y`。
  反向構造 DartFlow 需要每邊選兩個 dart——用 `β × Bool` 作 Δ 是乾淨做法。

### 風險/決策點(留給接手者判斷)

- 若 dart↔Graph 雙向翻譯基建太重(用戶擔心過的),**退路**:Statement.lean
  直接用 dart-style 的**元素級**陳述(darts=`β×Bool`,全部 Mathlib 原語),
  仍零我們庫詞彙、仍完全可核驗,但省去 `Graph α β` 適配。可先評估兩條路
  的基建量再選。用戶傾向:最乾淨地表達並導出,不為對齊而背重基建。

## 之後的路線(未動)

1. 完成 CDC 端口(本輪)。
2. **鳥瞰二 + 外向挖礦**(用戶採納):鄰域開問題檢索、Berge–Fulkerson/5-CDC/
   Petersen 染色族槓桿、codim 分層 ⟺ 染色層級、高維障礙、奇特徵版本。
   已登記於 ledger「鳥瞰議程」。
3. 凍結後段:`#min_imports` 二層 import 精簡、E2、F1(2) 反例、論文寫作。

## 模型交接建議(Fable 5 給用戶)

- **主力接手 = Opus 4.8**:本項目是重證明設計 + Lean 工程,需要強推理與
  長上下文連貫。Opus 4.8 最合適延續數學判斷與架構決策。
- **省 token 的活可下放**:純機械的 Lean 錯誤迭代、大檔重編譯等待、import
  批改——這類若想省用量,Sonnet 5 可勝任;但**設計決策(端口形態、
  dart↔Graph 取捨、鳥瞰數學判斷)建議留 Opus 4.8**。
- **GPT 5.6**:項目全程的數學規劃夥伴(見對話紀錄),數學品味極高;若要
  第二意見或獨立數學審視,值得諮詢,但 Lean 工程細節仍以 Opus 在庫內執行為宜。
- **回歸 Fable 5**:當 Opus/GPT 判斷遇到需要最高能力的節點(如新的結構性
  突破、論文核心論證成形、關鍵反例構造),且 Fable 有額度時回切。
- **工作紀律**(對所有接手模型):守 [[lean-cleanliness-mandate]](數學明徹、
  零 sorry、全generality、座標隔離、重機械儘量少儘量後)與 Release 鐵律。

謝謝合作。— Fable 5
