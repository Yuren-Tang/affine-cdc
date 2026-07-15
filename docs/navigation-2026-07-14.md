> **⛔ HISTORICAL / SUPERSEDED — 2026-07-15**
> 本文件完整保留作研究與工程史料，**不得作為目前導航、狀態或施工指令**。
> 現行入口為根目錄 `README.md` 與 `docs/00_READ_FIRST_ARCHITECTURE_CORRECTION.md`。
> 下文關於 loopless 最終命題、ambient-finite 最終語義、可選端到端整合、
> `cubic_flow_cdc` 作唯一 endpoint／waist，以及尚待選擇 loop convention 的說法，
> 均早於已核准而尚未實作的 Path A；除非現行入口明確認可，皆視為歷史文字。

---

> **⚠ SUPERSEDED (架構部分) — 2026-07-14**
> 本文件第 0 節「無條件 CDC = 論文 corollary、cdc-lean integration 僅為可選」的**架構結論已作廢**。
> 規範文件為 `docs/00_READ_FIRST_ARCHITECTURE_CORRECTION.md`(在任何衝突中它勝出)。
> **正確架構**:最終目標 = 無條件 `cycle_double_cover : CDCStatement`(端到端 machine-checked,
> 經**隔離整合包**組合已形式化外層 + 本庫 cubic-flow engine 達成,**必做**);`cubic_flow_cdc` 只是中間定理。
> 本文件的**礦脈條目(M1–M9)仍有效**,但以 `docs/02_MATHEMATICAL_UPDATE.md` 的更新版為準。

---

# AffineCDC 主導航與完整交接

**日期**:2026-07-14 **倉庫**:`Yuren-Tang/affine-cdc`
來源:用戶 + GPT 5.6 Sol 外審。本文件取代此前所有 P2/cdc-lean mandatory
integration/comparison 定位草稿。當前 Opus 4.8 施工;未來 Fable 5 回歸讀此。

## 0. 最重要的架構裁決

**數學與 Lean 核心完全自圓;與 OpenAI 原證明的關係由本庫內部的分類定理與數學說明
承擔,而不是由外部代碼依賴承擔。**

- **核心 Lean endpoint** = `cubic_flow_cdc : CubicFlowCDCStatement`
  (finite loopless cubic multigraph + nowhere-zero F₂³-flow ⟹ cycle double cover)。
  這是 AffineCDC 自己完整、自圓、machine-checked 的貢獻。
- **無條件 CDC = 論文 corollary**:把 `cubic_flow_cdc` 與經典 cubic reduction +
  已知 nowhere-zero flow theorem 組合,像普通論文引用已知定理。誠實區分:
  新 affine/Fano 核心與 cubic-flow CDC 已完全形式化;無條件 corollary 用已有文獻定理。
- **cdc-lean 端到端整合 = 未來可選、隔離 microproject**;非核心、非必做 P2、
  不阻塞 arXiv、永不成為核心依賴。先前升格為 mandatory P2 是漂移,已撤回。

## 1. 數學核心鏈

局部偶 affine-line families 分類 → edge quotient → affine gluing system
→ gauge classes / coker δ_f → codimension-one Fano compatibility
→ global glued supports → cycle double cover。
核心方程 `δ_f m = c_f`;自然 obstruction `[c_f] ∈ coker δ_f`;
Fano compatibility 在 codim 1 證 `[c_f] = 0`。這比 CDC 更一般;CDC 是導出。

## 2. 已完成 Lean(零 sorry,標準公理)

T1 局部 affine 分類 `localEquiv : Γ ≃ LocalEvenFamily W`(+ inj/surj、covers
formula、torsor、naturality);T3–T4 edge quotient 泛性 + gauge 分類 `coker δ`
+ dual criterion;T5–T7 cross-pairing bit、invariant functional uniqueness、
codim-1 branching identity、`DartFlow.exists_gluing(_of_finrank_three/_labels)`;
G CDC 抽取(σ-閉、每 dart 兩 supports、每 support 每頂點 0-或-2、explicit partner、
`rho = partner∘sigma`、`exists_cycle_double_cover`);`Decompose.lean` 標準 circuit
decomposition(finite even edge-set → edge-disjoint minimal even circuits)。

## 3. Comparison 的正確定位

**真正數學支柱是 T1,不是逐點翻譯。** T1 分類所有局部偶族,故原稿無論用何槽位/
排序/基準,只要產生局部偶族就自動是某 `Φ_W(m)`——嚴格強於逐點翻譯。
`slotFamily_eq_localFamily`(字典 `m⁰ = t + f(b)`)保留為:T1 API worked example、
座標↔gauge 參數字典、論文註腳。**不是**自圓支柱/主證明橋/引外庫理由/comparison 節主體。
論文措辭:"By the local classification theorem, every local even family—including
the one constructed in the original proof—is necessarily of the form Φ_W(m).
For the original slot normalization, the corresponding parameter is m⁰ = t+f(b)."

## 4. Statement / Port 角色

`Statement.lean` = 標準 CDC 目標的獨立語義 audit surface(讓外部確認 cycle/CDC/target
語義、無 darts/flow/planes 偷換)。**不要求核心當下 inhabit `cycle_double_cover :
CDCStatement`**。審計分兩塊:Statement 語義(`#print CDCStatement`…)+ 核心 theorem
(`#check cubic_flow_cdc`、`#print axioms cubic_flow_cdc`)。
`Port.lean` = 本庫語言 → Mathlib Graph 語義的橋;`graphDartFlow` 已完成;
`cubic_flow_cdc` 是當前 Opus 唯一核心工程主線。

## 5. P1 精確施工

從 `graphDartFlow` + `DartFlow.exists_cycle_double_cover`:(1) Γ-indexed dart
supports;(2) σ-閉投影為 edge supports;(3) 證 edge membership ⟺ 任一 endpoint
dart membership;(4) unique-partner/0-or-2 證 edge support `IsEven`;
(5) `exists_cycle_decomposition`;(6) 合併 Γ-indexed decompositions;
(7) exact-two dart coverage 證每 edge multiplicity=2;(8) 打包 `cubic_flow_cdc`。
完全不 import cdc-lean;獨立 axiom audit。

## 6. 論文誠實表述

正文證新 affine/Fano compatibility → 導出 cubic-flow CDC → 引經典 cubic reduction
+ flow theorem → 完整 CDC corollary。"We formalize the new affine/Fano core and
its implication to the cubic-flow form … Combined with the classical outer
reduction and flow theorem, this yields the CDC Conjecture." 不可模糊成
「整個歷史依賴閉包都在本庫重新形式化」(除非真做可選 integration microproject)。

## 7. cdc-lean 政策

不成核心依賴、不決定本庫圖編碼、不為對齊其槽位污染本庫、不阻塞 release。
未來可選 `affine-cdc-full-verification/`:reuse outer reduction + 替換 cubic cover
+ 端到端 kernel 驗證。是 comparison/verification product,非 AffineCDC 主體。

## 8. Loops 與有限性(P1 後,不阻塞)

Loops:當前 `IsEven` 用 `incidenceSet.ncard` 對 loop 只計一次,故語義只適 loopless。
不影響 affine core。候選:A 標準 loopless `CDCStatement`;B 另定 `PseudographCDCStatement`
(允許 loops,由 loopless 平凡推出);C 改 `IsEven` 為 loop-aware。P1 中途不展開。
有限 carriers:finite active graph 嵌 infinite ambient 只是表示問題;audit 最終可用
`V(G).Finite ∧ E(G).Finite`(或僅 `E(G).Finite`,允許無限孤立頂點)。真 edge-infinite
非本輪。Infinite extension(double rays/topological circles)列未來礦脈。

## 9–11. 研究礦脈(未來 Fable 5)

- **M1 solution moduli**:固定解 m₀,`Sol(D) = m₀ + ker δ_f`,solutions 是
  `ker δ_f`-torsor;全局常量 `M^{m+a}_s = M^m_{s+a}`。
- **M2 flow-aligned tension space**:`ker δ_f = d_G⁻¹(L_f)`;connected 上
  `ker δ_f/Γ ≅ im d_G ∩ L_f`;binary `B_f = {λ ∈ F₂^E : (λ_e f(e))_e 是 Γ-valued tension}`。
- **M3 K₄**:同 flow 兩 gauges `m₀(v)=0`、`m₁(v)=v` 分給三個 Hamilton 4-cycles /
  四個 triangles。
- **M4 rank-two boundary**:3-edge-colourable case 候選 `dim(ker δ_f/Γ) = |V|/2 − 1`,
  故 `2^{|V|/2−1}` 個 gauge classes;與 Hušek–Šámal counting conjecture 指數吻合
  (需查重 + injectivity proof)。
- **M5 genuine rank-three moduli**:`f=(F₁,F₂,F₃)`,`B_f = {λ : λF_i ∈ C*(G), i=1,2,3}`;
  研究 dim、Petersen/small snarks、zero/maximal moduli、CDC counting。
- **M6 codim-one sharpness**:codim 1 普遍成立;codim≥2 系統反例;extra obstruction 分類。
- **M7 rotation/surface**:`rho = partner∘sigma` 與 ribbon surfaces、orientability、
  genus、edge twists。
- **M8 sheaf/cohomology**:`δ_f : C⁰→C¹`,`[c_f] ∈ coker δ_f` 作 cellular sheaf /
  local coefficient obstruction 解讀。
- **M9 infinite compactness**:finite local subsystems ⟹ global gauge 的 compactness
  route;CDC endpoint 需 topological cycle semantics。

## 12. 模型分工

**Opus 4.8(當前)**:完成 `cubic_flow_cdc`;更新 Statement/Port/ledger/HANDOFF scope;
CI/lint/axiom audit;準備第一篇 release。不做:mandatory cdc-lean integration、
重型 loops wrapper、挖礦擴張。
**GPT-5.6**:外部語義審計;moduli/counting/codim 挖礦;紙面推導與文獻定位;文章取捨。
**未來 Fable 5**:回歸讀本文件,處理高推理節點:genuine rank-three moduli、codim-one
sharpness、counting theorem、surface/cohomology、compactness extension、論文核心敘事。

## 13. 當前唯一工程指令

完成並審計 `cubic_flow_cdc : CubicFlowCDCStatement`;恢復並記錄「核心自圓、comparison 由
T1 分類承擔、slot dictionary 只是 worked example、cdc-lean integration 僅為可選隔離驗證」。
