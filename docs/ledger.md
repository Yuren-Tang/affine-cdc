# 定理帳本(Theorem Ledger)

原則:逐塊封閉。每條定理記錄精確陳述、最弱假設、完整證明、依賴、來源分類
(屬原稿/原稿隱含/本文新增)。Lean 落後紙面一個模組。

## 總覽:七條定理規格(對話紀錄 §「現在的下一步」確立)

| # | 定理 | 紙面 | Lean |
|---|---|---|---|
| T1 | Local affine classification(局部偶族分類) | ✅ 封閉 | ✅ 完成(2026-07-12) |
| T2 | Naturality and torsor representation | ✅ 封閉 | ✅ 完成(2026-07-12) |
| T3 | Universal property of edge quotients | ✅ 封閉(2026-07-13 審定) | ✅ 完成(2026-07-12) |
| T4 | Gauge classification by coker δ_f | ✅ 封閉(2026-07-13 審定) | ✅ 完成(2026-07-13) |
| T5 | Well-definedness of the cross-pairing bit | ✅ 封閉(2026-07-13 審定) | ✅ 完成(2026-07-13) |
| T6 | Uniqueness of the invariant linear functional | ✅ 封閉(v2,任意 Γ;2026-07-13 審定) | ✅ E3 完成;E2 待(非阻塞) |
| T7 | Branching identity and global vanishing | ✅ 封閉(2026-07-13 審定) | ✅ **F2 終點 + F3 標籤形式完成** |
| G | Cycle double cover(抽取;dart 形式) | ✅(設計於架構圖;隨 Lean 同步) | ✅ **完成(2026-07-13):`exists_cycle_double_cover`** |

### 決策記錄(補充,2026-07-13,用戶授權定奪)

- **紙面 T3–T7 審定通過**(用戶:大致無問題,先前意見均已處理)。
- **真依賴/冗餘審查:做**,凍結期執行——`#min_imports` 逐檔精簡 import(兼上游化準備)
  + 逐定理試刪假設重編譯,與各稿「假設帳目」雙向核對。
- **GitHub + CI:現在**——主線落成即建帶時間戳公開記錄;CI = 構建 + 公理審計 +
  源碼掃描(`.github/workflows/ci.yml` 已備;遠端庫名/公開性待用戶一句話確認)。
- **Comparison 最終定奪:完全自圓**——(i) 庫終點原定 F2 + F3;(ii) **不對齊
  OpenAI 庫任何表述包括終定理**;(iii) 等價重構的形式承載 = 內化引理
  `slotFamily_eq_localFamily`(已完成):原稿槽位構造 = `Φ(t + f(b))`,
  顯式字典 **m⁰ = t + 中間槽位流值**。
- **修正(2026-07-13,用戶定奪):CDC 抽取入庫**——庫終點延伸為 G4
  (CDC,三次 + 給定 NWZ 流的條件形式;8-flow 存在性與三次化約仍引文獻)。
  設計(見[架構圖](架構圖.md)):G1 每頂點 0-或-2(T1 覆蓋計數拉回);
  G2 **圈 = ρ-軌道**,`ρ := 頂點配對 ∘ σ`(dart 語言下圈分解 = 置換軌道
  分解,免頂點路徑形式化——規範自由的又一增益);G3 每邊恰兩次(B1);
  G4 打包。凍結順延至 G 完成後。
- **Release 政策(鐵律)**:任何 tag / GitHub Release / Zenodo 存檔之前,
  必須完成狀態交用戶審查——嚴禁產生髒 DOI。日常只推 commit,不 tag。
- **分支設計**:`main`(穩定、CI 綠、可審查)/ `dev`(整合開發)。
- **依賴審查工具鏈**:`#min_imports`(Mathlib 命令,逐檔最小 import)、
  `lake exe graph`(importGraph 包,模組級依賴圖,本庫已有此依賴)、
  逐定理試刪假設重編譯;定理級 JSON 依賴圖生成器(用戶外部工具/Erdős 306
  經驗)在凍結期接入。
- **runLinter 實測結論(2026-07-13)**:Batteries env linters(含
  `unusedArguments` 逐定理未用假設檢查)全庫 17 模組**首輪全綠**——
  「逐定理刪」的正規替代已落地並接入 CI(每次推送常駐審查)。
- **shake 實測結論(2026-07-13)**:**內部依賴圖的判斷可信且有價值**
  (已採納:Dart 只需 LocalClassification;Fano 顯式引其真依賴
  Rank/Branching/Gauge;Cover 顯式引 Fano/OppositeFiber;DualConfig 只需
  Basic;Invariance 顯式引 DualConfig+LocalClassification——內部圖與架構
  圖紙一致化);**Mathlib-級 import 精簡不可信**(漏戰術依賴如 `abel`、
  漏 `Dual.Lemmas` 等)——Basic/Gauge 維持 `import Mathlib`,二層精確化
  留給檔內運行的 `#min_imports`(凍結後段)。`scripts/noshake.json` 已建。

### 決策記錄:與 OpenAI Lean 的關係(2026-07-12 定調,經用戶確認方向)

**骨幹絕對獨立;「comparison layer」= 數學內化,不是代碼依賴。**

1. 紙面級對照(源碼行號對應表)——已做,見 [comparison-notes.md](comparison-notes.md)。
2. **數學內化(正式的 comparison 定義)**:在本庫內抽象定義「槽位排序局部基準
   資料」(原稿式 (2) / `localBase` 的數學內容),證明其族 = 某 `Φ(m⁰)` 且
   `[d] ~ c_f`(T4 文檔含草稿)。等價主張由此在本庫封閉,不引用外部代碼。
3. 代碼級橋接(import cdc-lean、kernel 打通其 CDC 終定理)**降級為項目末期
   可選的隔離微項目**(自帶 lakefile、用其 pin`9a9483a`),永不成為本庫依賴。
4. 本庫 Lean 終點 = **Fano 相容性定理 `[c_f] = 0`**(自有極小圖層);
   CDC 為論文 remark。理由:等價是數學定理不是構建鏈接;獨立性保留 Mathlib
   上游化選項(char2 工具、torsor、商泛性皆 Mathlib 級);CDC 終點認識論冗餘。
5. 設計後果:T7 圖層用**半邊(dart)+ 對合 + 頂點劃分**形式化——原庫連圖
   編碼都有座標(`endAt e 0/1`、`edgeAt v i` 槽位),半邊形式是圖層的規範自由
   表示,「考古」延伸到組合結構本身。

---

## T1 — 局部偶族的自然表示定理 ✦ 已封閉、Lean 完成

**設定**:`Γ` 任意 F₂-向量空間(不要求有限、有限維);`W ≤ Γ` 平面;
`D = W ∖ {0}`(三方向,兩兩之和為第三)。方向 `h` 的線 = 二點集 `{p, p+h}`。

| 紙面 | 陳述 | Lean 名稱 | 狀態 |
|---|---|---|---|
| 定理 A | `Φ_W : Γ ≅ L_Γ(W)` 雙射 | `localEquiv : Γ ≃ LocalEvenFamily W` | ✅ |
| — 主計算 | `s ∈ Φ_W(m)_h ⟺ s+m ∈ W ∖ {0,h}` | `covers_localFamily_iff` | ✅ |
| — 良定/單射/滿射 | 覆蓋數 0 或 2;刪去點唯一;奇偶步 | `isEven_localFamily`, `localFamily_injective`, `exists_localFamily_eq`, `covers_parity` | ✅ |
| κ 無選擇性 | `κ_h` = 另兩方向公共類 | `IsPlane.kappa`, `kappa_eq`, `kappa_ne_zero` | ✅ |
| 推論 A3 | 對向纖維;coset = 二點集 | `localFamily_points`, `coset_eq_pair`, `not_covers_self`, `localFamily_points_pair` | ✅ |
| 假設橋接 | `finrank W = 2 → IsPlane W` | `IsPlane.of_finrank_eq_two` | ✅ |

## T2 — 自然性與 torsor 表示 ✦ 已封閉、Lean 完成

「局部解空間 = 與 Γ 的自然等變表示定理」(canonical representation,非 universal property——見對話 §四種必然性)。

| 紙面 | 陳述 | Lean 名稱 | 狀態 |
|---|---|---|---|
| 推論 A1 | 平移等變 `Φ_W(m+a) = a⋅Φ_W(m)` | `localFamily_translate`, `IsEven.translate` | ✅ |
| — torsor 打包 | `L(W)` 是 Γ-torsor;`Φ_W` 仿射同構 | `localTorsor`, `localTorsor_vadd`, `localAffineEquiv` | ✅ |
| 推論 A2 | 對 `T : Γ ≃ₗ Γ'` 全套傳輸 + 交換圖 `T_*Φ_W(m) = Φ_{TW}(Tm)` | `Dir.map/comap`, `lineEquivAt`, `mapFamily`, `IsEven.map`, `IsPlane.map`, `mapFamily_localFamily`, `localEquiv_naturality` | ✅ |

註:torsor 結構不能是全局 instance(平面性是 Prop 假設)——`localTorsor` 為 def,
`localAffineEquiv` 帶顯式 instance 參數。這回答了對話中「解集是否有現成
affine-space instance」之問:**沒有,但可以乾淨打包**。

## T3 — 邊商泛性 ✦ 紙面草案待審定 ✦ Lean 完成

規格全文:[T3-邊商泛性.md](T3-邊商泛性.md)。Lean(`EdgeQuotient.lean`):

| 紙面 | 陳述 | Lean 名稱 | 狀態 |
|---|---|---|---|
| B1 | 二點集 = 陪集 | `coset_eq_pair`(OppositeFiber) | ✅ |
| B2 | 消滅 h 的線性映射唯一經 `LineSpace h` 分解 | `lineLift`, `lineLift_lineMk`, `lineLift_unique` | ✅ |
| B3 | `W` 的像 = `{0, κ_h}`;κ 唯一非零 | `kappa_mem_map`, `eq_kappa_of_ne_zero`, `map_eq_pair` | ✅ |
| B4 | 標籤公式 `[m]+κ`;偶族的唯一仿射實現 | `localFamily_apply`, `existsUnique_label` | ✅ |

## T4 — coker δ 規範分類 ✦ 紙面草案待審定

規格全文:[T4-規範分類.md](T4-規範分類.md)。Lean(`Gauge.lean`,任意域):

| 紙面 | 陳述 | Lean 名稱 | 狀態 |
|---|---|---|---|
| C1 完整性 | `c ~ c' ⟺ [c]=[c']`;不變量必經 `[c]` | `gaugeEquiv_iff`, `invariant_eq_of_gaugeEquiv` | ✅ |
| C1 分類 | `C¹/~ ≅ coker δ` | `gaugeSetoid`, `gaugeClassesEquiv` | ✅ |
| C1 障礙 | 可解 ⟺ `[c]=0` | `exists_solution_iff` | ✅ |
| C2 對偶判準 | 任意維(場上射影商) | `mem_range_iff_forall_dual`, `exists_solution_iff_forall_dual` | ✅ |
| C3 黏合方程 | `(δ_f m)_e = c_f(e)`(依賴圖層) | — | ⬜ 隨 T7 圖層 |

另含 `[d] ~ c_f`(原稿 d_e 與天然類同規範類)的 comparison-layer 核心引理草稿。

## T5 — 交叉配對位元良定 ✦ 紙面草案待審定 ✦ Lean 完成

規格全文:[T5-交叉配對.md](T5-交叉配對.md)。Lean(`DualConfig.lean`,任意 Γ):

| 紙面 | 陳述 | Lean 名稱 | 狀態 |
|---|---|---|---|
| — 空間 | `K(W)` 是子模(求和條件以「和為零三元組」無枚舉表述) | `dualConfig`, `mem_dualConfig` | ✅ |
| D1 | 六個交叉值相等 | `eval_eq_of_ne`, `eval_swap`, `cross_eq` | ✅ |
| D2 | β 線性 | `crossBit`, `crossBit_eq`, `crossBitL` | ✅ |
| D3 | `β = 0 ⟺ 全部 η_h 消滅 W` | `crossBit_eq_zero_iff` | ✅ |

## T6 — 不變線性泛函唯一性 ✦ 紙面草案 v2 待審定(升格)

規格全文:[T6-唯一性.md](T6-唯一性.md)。**v2 藍圖變更(2026-07-13)**:升格為
**任意 F₂-向量空間**的定理,統一剪切證明——關鍵同構 `Hom(C,W) ≅ C* × C*`
(經 T3 B3 的 λ 泛函),在 β=1 配置上剪切獨立打亂兩個 K₀-座標 ⟹ 不變泛函
的 K₀-部分為零 ⟹ `ℓ ∈ {0, β}`。且只需剪切子群不變(強於全 H)。原 dim-3
證明成為 `C* = F₂` 特例。**由此 T1–T6 全部與維數無關;dim Γ = 3 唯一進場點
= T7 F1,且在彼處是精確刻畫。**

Lean(`Invariance.lean`,任意 Γ):

| 紙面 | 陳述 | Lean 名稱 | 狀態 |
|---|---|---|---|
| — 剪切作用 | `η_h ↦ η_h + η_h∘s` 保持合法性 | `shearConfig`, `shearConfig_mem`, `ShearInvariant` | ✅ |
| E1(隱式) | β=1 的顯式配置(選擇隔離於 `sepFun`/`projW`) | `baseConfig`, `baseFun_*`, `crossBit_baseConfig` | ✅ |
| E3 crux | 不變 ⟹ 消滅 `ker β`(η 的伴隨剪切 + 關鍵恆等式) | `ShearInvariant.eq_zero_of_crossBit_eq_zero` | ✅ |
| E3 | `ℓ = ℓ(η₁) • β`;`ℓ ∈ {0, β}` | `ShearInvariant.eq_smul_crossBitL`, `.eq_zero_or_eq_crossBitL` | ✅ |
| E2 | 全 H-不變性(需 Aut(Γ,W) 作用定義) | — | ⬜ 待辦(非阻塞;紙面已證) |

## T7 — 分支恆等式與全局消失 ✦ 紙面草案待審定

規格全文:[T7-分支恆等式.md](T7-分支恆等式.md)。F0 dart 圖層(半邊+對合+三次
劃分;`Q_{σd} = Q_d` 是定義相等——原庫的 `endAt`/`edgeAt` 座標在此消失);
F1 分支恆等式 `β = #{η_h ≠ 0} mod 2` **⟺ codim W = 1**(dim 3 的精確刻畫,
含 codim ≥ 2 反例);F2 全局消失(Fano 相容性定理,經 T3–T6 語言的原稿
Lemma 2.2);F3 全局偶族(CDC 介面 = remark,依決策記錄)。

Lean 進度(`Branching.lean` 等):

| 紙面 | 陳述 | Lean 名稱 | 狀態 |
|---|---|---|---|
| F1 前置 | codim 1 ⟹ `W` 的零化子唯一非零元素 | `annihilator_unique` | ✅ |
| F1(1) | `β = Σ nzBit`(任意和零三元組形式) | `crossBit_eq_parity`, `nzBit` | ✅ |
| F1(2) | codim ≥ 2 反例(恆等式失效) | — | ⬜(低優先;紙面已證) |
| 橋接(逆) | `IsPlane → finrank W = 2`(與 `of_finrank_eq_two` 合為等價) | `IsPlane.finrank_eq_two`(Rank.lean) | ✅ |
| F0 | dart 結構(σ 對合 + 頂點平面 + `cubic` 雙射)、`next` 伴 dart、`delta`、`cfam`、`theta/psi/vertexConfig` | `Dart.lean`:`DartFlow`, `dartEquiv`, `next`, `delta`, `cfam` | ✅ |
| C3 | `cfam = κ_d + [κ_{σd}]`(黏合方程之天然形式) | `cfam_eq_kappa` | ✅ |
| **F2** | **Fano 相容性定理:`∃ m, δ_f m = c_f`(終點)** | `DartFlow.exists_gluing`(codim-1 形式)、`exists_gluing_of_finrank_three` | ✅ |
| F3 | 全局偶族打包(C3+T1 組合的 API) | — | ⬜ 待辦(非阻塞) |

工程註:codim-1 假設以 `finrank (Γ ⧸ W) = 1` 形式進入;`exists_gluing_of_finrank_three`
經 `IsPlane.finrank_eq_two` + `Submodule.finrank_quotient_add_finrank` 翻譯
`finrank Γ = 3`。F1 陳述在「任意和零三元組」上,無需 `Fintype (Dir W)`。
**dart 層設計驗證**:dart-逐分量陳述系統(d-方程與 σd-方程各自在自己的商中,
邏輯等價而無需形式化該等價)徹底避開 `Q_{σd} = Q_d` 的類型傳輸;`next`(伴 dart)
以 `exists_companion + choose` 隔離選擇,`cfam_eq_kappa` 證其值無選擇。
F2 證明 = 對偶判準(C2)+ 逐頂點 `vertexConfig ∈ dualConfig`(T5)+ 交叉值 = β
(D1)+ 分支恆等式(F1)+ σ-對合雙端計數(`Finset.sum_ninvolution`)。

---

## CDC 審計端口(FLT Statement/Port 模式,進行中)

目標:圖論專家在獨立 audit 裡快速核驗「聲稱的 CDC 就是標準 CDC、只依賴 Mathlib」。

| 檔案 | 內容 | 狀態 |
|---|---|---|
| `Statement.lean` | **審計面**:只 import Mathlib、零本庫詞彙。`CDCStatement` 陳述於 Mathlib 多重圖 `Graph α β`;cycle = 極小非空偶邊集(標準 matroid circuit,對齊 cdc-lean 嚴格度);CDC = cycle 多重集每邊恰覆蓋兩次;cubic + nowhere-zero F₂³-flow 全內聯定義。誠實限定於「cubic+flow ⟹ CDC」,8-flow 與三次化約為引用的古典輸入(顯式缺席)。 | ✅ 編譯 |
| `Decompose.lean` | 圈分解(Veblen,強歸納):有限偶邊集 → cycle 多重集,每邊恰覆蓋一次。把偶 2-正則子圖轉為真正的 cycle 覆蓋。 | ✅ 編譯 |
| `Port.lean` | Graph → DartFlow 橋 + 組裝。已完成:三鄰邊提取(finsum 守恆 → a+b+c=0)、**頂點平面**(`vertexPlane`,由流值 Klein 三元組證 `IsPlane`,經 span{a,b} + finrank=2)。 | 🟡 平面部分編譯 |

**Port 剩餘**(mechanical but lengthy):cubic 雙射欄(鄰邊 ≃ Dir(平面),需全值互異 + 基數 3=3)、完整 `DartFlow`(V=頂點子型 `{x//x∈V(G)}`,σ 經 `Inc.other`)、覆蓋組裝(`exists_cycle_double_cover` 的 M → 邊集偶性 → `exists_cycle_decomposition` → 合併 → 每邊兩次)、最終 `theorem cdc : CDCStatement`。之後 `AuditStatement.lean`(`#print CDCStatement` + `#print axioms cdc`)+ CI 加審計步。

## 架構圖紙

真數學依賴圖(存在線/必然線/橋三部結構、唯一 dim-3 閘門、選擇隔離點、
G-計劃):[架構圖.md](架構圖.md)。

## G — CDC 抽取 ✦ Lean 完成(2026-07-13)

`Cover.lean` + `Cycle.lean`:

| 節點 | 陳述 | Lean 名稱 | 狀態 |
|---|---|---|---|
| G0 | 支集 σ-閉(兩端點集一致;同代表元技巧) | `Msupp`, `Msupp_sigma`, `mem_Msupp_iff_master/rep/glued` | ✅ |
| G1 | 頂點 0-或-2:伴 dart 顯式公式 `f(partner) = (s+m_u)+f d` | `partnerD`, `partnerD_*`, `Msupp_vertex_unique` | ✅ |
| G2 | 旋轉 `ρ = partner∘σ`,雙側逆 `σ∘partner`;**圈 = ρ-軌道** | `rho`, `rhoInv`, `rho_*` | ✅ |
| G3 | 每 dart 恰在兩個支集(= 每邊恰兩次) | `setOf_mem_Msupp`, `ncard_setOf_mem_Msupp` | ✅ |
| G4 | **CDC(dart 形式)**:σ-閉、雙層、逢頂 2-正則、帶旋轉見證 | `exists_cycle_double_cover` | ✅ |

註:G1 的伴 dart 無選擇(第三點顯式公式);G2 的「圈分解 = 置換軌道分解」
是 dart 形式化的又一結構增益(免頂點路徑);G4 之於經典 CDC 表述的翻譯
= 論文一段(σ-閉 dart 集 + 0/2 度數 + 旋轉 ⟺ 圈之多重集)。

## 鳥瞰議程(收官前後兩輪全局考察的線索池)

時機:第一輪 = 七條審定後、T6/T7 Lean 之前(已做);第二輪 = **G 完成後、
論文前(下一項)**,含**外向挖礦**(2026-07-13 用戶採納):檢索鄰域開問題、
重審不乾淨的閉問題、跨域連結/基建轉接——敵我雙向交叉探查。已登記礦脈:
codim-0 邊界 ⟺ 三邊可染色(Szekeres 情形)、高維障礙分類、
Berge–Fulkerson/5-CDC/Petersen 染色一族的槓桿檢查、奇特徵版本(0-或-p 覆蓋)。

1. **codim-1 現象的定位**:T6 唯一性任意維成立、T7 計數表示恰在 codim 1——
   CDC 機制是否「就是」codim-1 現象?高 codim 的正確替代物(若有)是什麼?
2. **細胞層/上同調讀法**:`δ_f : C⁰ → C¹` 是圖上係數層的 Čech 微分;
   `[c_f]` 是否某個自然層類(cup/transgression)?K(W) 的正合列
   `0 → ((Γ/W)*)² → K(W) → F₂ → 0` 是否對偶層的 stalk 序列?
3. **dart 對偶**:頂點平面 W_v(3 方向)與邊商 Q_e——flag 結構上的
   點-線對偶;和 Fano 平面的關聯是否不止修辭?
4. **|L(W)| = |Γ| 的計數/groupoid 讀法**:torsor 性是否有 species 層面的解釋?
5. **4-cover → 2-cover 壓縮**:Bermond–Jackson–Jaeger 的 circuit 4-cover
   與我們的 torsor 圖景——「4→2」是否 = 「Γ-torsor → 商掉 W 方向」?
6. **上游化候選審計**(工程):char2 模引理、IsPlane/Klein 三元組、
   torsor 打包、E3 的剪切引理——收官後逐一對 Mathlib 現狀查缺。

## 註釋政策(2026-07-13 定)

- 帳本編號(T#/B#/C#/D#/E#/F#)**允許且鼓勵**出現在 docstring/註釋——它們是
  Lean↔帳本的活引用;統一格式 `**D1**`/`(T3)`,終稿定號時一次機械替換。
- **聲明名永不用帳本編號**(始終結構化命名:`localEquiv`、`crossBit`、…)——
  這是防返工的唯一不變式;註釋洗滌零成本,改聲明名才是重構。

## Lean 薄切片的工程發現(回饋紙面)

1. **線的原語 = 邊商**:`Γ ⧸ span{h}` 為原語、二點集為導出(`coset_eq_pair`),
   定理 A 全程是商空間短計算,避開 Finset/cardinality API。T3 已按此起草。
2. **torsor 陳述**:`Equiv` + 等變性引理承載數學內容;`AddTorsor`/`AffineEquiv`
   打包可行但需 def(非 instance)。
3. **偶性表述**:定義層 `Even (coverSet P s).ncard`(無序、無 Fintype);
   使用層 `covers_parity` 轉布爾推理。
4. **平面性**:內在 `IsPlane`(Klein 三元組)進主線;`finrank = 2` 橋接與
   座標/`decide` 隔離在 `Rank.lean`。
5. **陷阱記錄**:`rcases rfl` 在兩側皆變量時消去方向不確定——分支內顯式 `rw [h1]`;
   `Ne` 目標下 `rw` 不穿透——先 `intro` 再 `rw at`;section `variable` 只在證明體
   使用時需 `include`;`push_neg` 已棄用(改寫為顯式構造)。

## 假設帳目(T1–T3)

- 必須:F₂(`Module (ZMod 2) Γ`);T1/T2/B3/B4 另需 `W` 平面。
- 不需要:`dim Γ = 3`、`Γ` 有限、圖、flow、方向排序、對偶。

## 基礎設施備忘

- `lean/` 獨立 Lake 項目,只 require mathlib v4.31.0(與 Erdős 項目同 rev;
  `.lake/packages` 由 APFS clonefile 複製,含全部 olean)。
- 構建:`cd lean && lake build`;單檔迭代 `lake env lean AffineCDC/<file>.lean`(~100s)。
- import 精簡屬論文期打磨,現階段 `import Mathlib`。

## 驗證記錄

- 2026-07-12(T1):五檔編譯,零 `sorry`;`localEquiv`、`localFamily_translate`、
  `localFamily_points`、`IsPlane.of_finrank_eq_two` 只依賴
  `propext, Classical.choice, Quot.sound`。
- 2026-07-12(T2):`Naturality.lean`、`Torsor.lean` 編譯,零 `sorry`;
  `mapFamily_localFamily`、`localTorsor`、`localAffineEquiv`、`IsEven.map`
  公理同上。
- 2026-07-12(T3):`EdgeQuotient.lean` 編譯,零 `sorry`;B2–B4 公理同上。
  新增 `Audit.lean`:`lake env lean AffineCDC/Audit.lean` 一鍵列印 T1–T3
  頭號定理公理足跡(對齊 cdc-lean 的審計慣例)。
- 2026-07-12(材料):取得原證明/prompt/cdc-lean(pin 記錄與逐項對應見
  [comparison-notes.md](comparison-notes.md));原庫同 toolchain v4.31.0、
  Mathlib pin 不同(`9a9483a…` vs 我們 `fabf563…`)。
- 2026-07-12(T4 抽象部):`Gauge.lean` 編譯,零 `sorry`,公理標準;
  C1/C2 對**任意域**成立(比 F₂ 更廣,按紙面最弱假設)。
- 2026-07-13(T5):`DualConfig.lean` 編譯,零 `sorry`,公理標準;任意 Γ。
- 2026-07-13(基建):外層倉庫 `.git/info/exclude` 屏蔽 `AffineCDC/`(不動
  Erdős 分支);`AffineCDC/.git` 初始化為獨立倉庫(`.gitignore`:`sources/`、
  `lean/.lake/`);首次 commit 待用戶指示。
- 2026-07-13(藍圖):T6 升格為任意 Γ(剪切統一證明);T7 起草完成——
  **七條規格全部成稿**,進入審定+鳥瞰窗口。
- 2026-07-13(鳥瞰第一輪):[鳥瞰-1.md](鳥瞰-1.md)——藍圖無結構性變更;
  新增兩個論文詞典小節(細胞層讀法、Fano 關聯幾何);高維障礙分類確認為
  論文後支線;species 讀法棄;4-cover 對比緩至寫作期;新線索:E3′ 的
  表示論定位(unipotent 不變量)。
- 2026-07-13(T6 E3):`Invariance.lean` 編譯(首試即過),零 `sorry`,
  公理標準,任意 Γ;E2(全 H)列為非阻塞待辦。
- 2026-07-13(T7 F1):`Branching.lean` 編譯(首試即過)——dim Γ = 3 以
  codim-1 內在形式**首次且唯一**進入 Lean 庫;`annihilator_unique` 是唯一
  消費該假設的引理。`Rank.lean` 補逆橋接 `IsPlane.finrank_eq_two`
  (注意 Mathlib 現名:`Module.Basis.mk`、`Module.finrank_eq_card_basis`;
  子類型強制的展開器陷阱:前向 `have := Subtype.ext_iff.mp e` 繞開)。
- 2026-07-13(G,**CDC 落成**):`Cover.lean`、`Cycle.lean` 編譯,
  `exists_cycle_double_cover` 公理標準;全庫 17 檔零 `sorry`。
  內化引理降級為「T1 之 worked example + 字典注」(2026-07-13 用戶判準:
  等價重構主張的數學承載 = T1 分類本身)。
- 2026-07-13(F3 + 內化):`exists_gluing_labels`(F3 標籤形式)、
  `Comparison.lean`(`slotFamily_eq_localFamily`,m⁰ = t + f(b) 字典)編譯,
  公理標準。CI workflow 就緒。
- 2026-07-13(T7 F0/C3/F2,**主線收官**):`Dart.lean` + `Fano.lean` 編譯;
  終點定理 `DartFlow.exists_gluing`(+ `_of_finrank_three`)公理標準;
  全庫零 `sorry`/`native_decide`/新公理,審計檔覆蓋 T1–T7 全部頭號定理。
  剩餘皆非阻塞:E2、F1(2)、F3 打包、comparison 內化引理(`[d] ~ c_f`)、
  紙面 T3–T7 審定、凍結期打磨(import 精簡、註釋洗滌、上游化審計)。
