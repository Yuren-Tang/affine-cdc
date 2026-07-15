> **⛔ HISTORICAL / SUPERSEDED AS CURRENT GUIDANCE — 2026-07-15**
> 本文件完整保留作數學發展史料，其中若干結果仍可能有獨立價值；但其論文主幹、
> 工作次序與「完成無條件 CDC 鏈後再處理」等狀態語句，**不再控制目前項目**。
> 現行入口為根目錄 `README.md` 與 `docs/00_READ_FIRST_ARCHITECTURE_CORRECTION.md`。
> 已核准而尚未實作的 Path A、even-cover／cut-even collapse／一次最終 decomposition／
> loop reinsertion 主幹，在任何衝突中優先於下文。

---

# 02 — Mathematical update since Opus paused

This file is informational. It records results found after the engineering pause. They should influence the paper and future Lean plan, but they must not derail the immediate P1/P2 engineering chain.

---

## 1. Solution moduli

For the gluing equation

\[
\delta_fm=c_f,
\]

once one solution \(m_0\) exists:

\[
\operatorname{Sol}=m_0+\ker\delta_f.
\]

Global constants lie in the kernel and merely translate support labels:

\[
M^{m+\underline a}_s=M^m_{s+a}.
\]

Modulo constants, the moduli space is a binary code \(\mathcal B_f\).

---

## 2. Flow-aligned tension / Schur-code theorem

Let \(\mathcal C(G)\) be the binary cycle code and let

\[
\mathcal F_f=\{\ell\circ f:\ell\in\Gamma^*\}
\le\mathcal C(G).
\]

For componentwise product `*`:

\[
\boxed{
\mathcal B_f=(\mathcal C(G)*\mathcal F_f)^\perp.
}
\]

Hence:

\[
\dim\mathcal B_f
=
|E|-\dim(\mathcal C*\mathcal F_f).
\]

This is coordinate-free and invariant under change of basis in \(\Gamma\).

---

## 3. Fano Hodge self-duality

For \(\Gamma=\mathbf F_2^3\), the unique nonzero volume form

\[
\omega:\Lambda^3\Gamma\to\mathbf F_2
\]

gives a local isomorphism:

\[
H_W(a)_h(x)=\omega(a,h,x),
\]

\[
\boxed{
H_W:\Gamma\cong\operatorname{dualConfig}(W).
}
\]

`crossBit` is simply the quotient bit detecting whether \(a\notin W\).

Globally:

\[
\boxed{
\ker\delta_f\cong\operatorname{Stress}(f).
}
\]

Constants correspond to canonical determinant stresses.

The existing T7 proof becomes:

```text
local Fano incidence/Hodge identity
+ global edge-handshake cancellation
= obstruction vanishing.
```

This is a strong candidate for the conceptual presentation of the first paper. The current Lean proof remains valid; a Hodge refactor is optional and should wait until the final theorem engineering is stable.

---

## 4. Exact sharpness in higher rank

For a legal local configuration \(\eta\), define the order-independent exterior defect:

\[
\mathfrak D_W(\eta)
=
(1+\beta(\eta))
(\eta_x\wedge\eta_y)
\in\Lambda^2\operatorname{Ann}(W).
\]

The branching identity fails exactly when this defect is nonzero.

Therefore it holds for all local configurations iff:

\[
\boxed{\operatorname{codim}W\le1.}
\]

This gives a complete local classification, not merely an example of failure.

---

## 5. Global higher-rank obstruction

For every equilibrium stress \(\psi\):

\[
\boxed{
\langle\psi,c_f\rangle
=
\sum_v
\mathbf1_{\mathfrak D_{W_v}(\eta_v)\ne0}.
}
\]

Thus compatibility means every stress has an even number of defective vertices.

An explicit rank-four nowhere-zero flow on \(K_{3,3}\) and an equilibrium stress with obstruction \(1\) have been found. Therefore automatic compatibility genuinely fails globally in rank four.

This proves that rank three/codimension one is mathematically sharp.

---

## 6. Gauge–embedding correspondence

A solution of the gluing equation is equivalent to a strong cellular embedding with Γ-valued face potentials satisfying:

\[
f(e)=t(F_e^+)+t(F_e^-).
\]

More precisely:

\[
\boxed{
\operatorname{Sol}(\delta_fm=c_f)/\Gamma
\cong
\{
\text{strong embeddings on which }f\text{ is dual-exact}
\}.
}
\]

Cohomological form:

\[
[f]_\Sigma=0\in H^1(\Sigma;\Gamma).
\]

Consequences:

- the moduli code counts flow-compatible strong embeddings;
- every flow on a plane cubic graph is compatible in every ambient rank;
- the affine supports recover facial circuits grouped by equal face potential;
- different gauges may change surface topology.

For \(K_4\), the two rank-two gauge classes give:

- sphere embedding with four triangular faces;
- projective-plane embedding with three Hamiltonian faces.

---

## 7. Rank-two counting

For a connected 3-edge-colourable cubic graph on \(n\) vertices:

\[
\boxed{
\dim\mathcal B_f=\frac n2-1.
}
\]

Via the embedding correspondence, a fixed Tait flow yields:

\[
\boxed{
2^{n/2-1}
}
\]

distinct flow-compatible strong embeddings and facial circuit double covers.

This appears to prove the Hušek–Šámal lower bound for the 3-edge-colourable class, subject to convention alignment and literature checking.

---

## 8. Computation archives

Reproducible standard-library Python scripts exist for:

- rank-three moduli enumeration;
- local/global Hodge verification;
- higher-rank obstruction census.

Verified counts include:

- Petersen rank-three full-support flow subspaces:
  \(170\), with \(b_f=0,1,2\) distribution \(80,80,10\);
- rank-four Petersen flows:
  \(81\) compatible, \(200\) incompatible;
- rank-four cube flows:
  all \(19\) compatible, explained by planarity.

---

## 9. Suggested paper upgrade

The first paper can now be organized around mechanism rather than only extraction:

1. local affine classification;
2. gauge/cokernel obstruction;
3. gauge–embedding correspondence;
4. Fano Hodge self-duality;
5. automatic rank-three compatibility;
6. higher-rank exterior defect and explicit sharp counterexample;
7. cycle double cover as facial cover of the constructed embedding.

Do not attempt to formalize all of this before completing the unconditional CDC theorem chain. Record it in the paper plan and select low-cost Lean lemmas later.
