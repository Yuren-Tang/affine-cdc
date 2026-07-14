# 00 — READ FIRST: definitive architecture correction

**Date:** 2026-07-14  
**Repository:** `Yuren-Tang/affine-cdc`  
**Latest visible commit:** `596d488f3c448c385ad361f57df1532030a9f140`  
**Purpose:** overwrite the architecture currently remaining in the truncated Opus context.

---

## 1. The last Opus understanding is superseded

The following sentence is **wrong** and must not guide further work:

> “The endpoint is `cubic_flow_cdc : CubicFlowCDCStatement`; unconditional CDC is only a paper corollary; cdc-lean integration is optional and not a release prerequisite.”

The correct architecture is:

\[
\boxed{
\texttt{cycle\_double\_cover : CDCStatement}
}
\]

is the final end-to-end theorem and audit target.

`cubic_flow_cdc` is only an intermediate macro-Port theorem:

\[
\text{cubic graph + nowhere-zero }\mathbf F_2^3\text{-flow}
\Longrightarrow
\text{standard cycle double cover}.
\]

It is useful and should be completed, but it does not replace the unconditional statement.

---

## 2. Why `Statement.lean` exists

`Statement.lean` was deliberately rewritten as a Mathlib-only, unconditional CDC audit surface:

```lean
def CDCStatement : Prop :=
  ∀ {α β : Type} [Finite α] [Finite β] (G : Graph α β),
    Loopless G → Bridgeless G →
    ∃ 𝒞 : Multiset (Set β), IsCycleDoubleCover G 𝒞
```

It contains no cubic, flow, dart, plane or gauge vocabulary.

The purpose of this work was not merely to display a paper corollary. The final integration theorem must directly inhabit this proposition:

```lean
cycle_double_cover : CDCStatement
```

The final audit is therefore:

```lean
#print CDCStatement
#check cycle_double_cover
#print axioms cycle_double_cover
```

plus a proof-path audit.

---

## 3. Core independence and full theorem closure are compatible

Use a two-package architecture.

### A. AffineCDC core

The core remains completely self-contained and must never depend on `openai/cdc-lean`.

Its chain is:

```text
T1 local classification
→ gauge / cokernel obstruction
→ Fano compatibility
→ dart-level indexed even cover
→ Graph-to-DartFlow port
→ cubic_flow_cdc
```

### B. Isolated end-to-end integration

A separate integration package/microproject may depend on the formalized outer infrastructure.

It composes:

```text
bridgeless graph
→ cubic reduction
→ nowhere-zero Γ-flow input
→ AffineCDC cubic-flow cover
→ cycle_double_cover : CDCStatement
```

This isolated integration **is required** for claiming that the complete unconditional CDC theorem is machine-checked end to end.

It is not a dependency of the core, but it is a deliverable of the overall project.

---

## 4. Do not shortcut the proof path

The integration may reuse the old formalized outer reduction, but it must not simply call the old complete CDC endpoint.

Required:

- follow/reuse the outer reduction infrastructure;
- replace the old cubic cover engine with the AffineCDC construction;
- expose a dependency/proof-path audit showing that the new affine core is genuinely used.

Forbidden shortcut:

```lean
exact CDCLean.cycleDoubleCover_of_bridgeless ...
```

or any equivalent direct invocation of the old final theorem.

---

## 5. Comparison is a separate issue

The mathematical statement “this is an equivalent reconstruction of the original local construction” is carried primarily by T1:

> T1 classifies all local even affine-line families.

Therefore the original slot construction is automatically some `Φ_W(m)`.

The explicit lemma

```lean
slotFamily_eq_localFamily
```

and dictionary

\[
m^0=t+f(b)
\]

remain valuable as a worked example and concrete dictionary, but are not the structural pillar and are not a reason to import external code.

Keep these two questions separate:

1. **comparison of mathematical constructions** — handled internally by T1;
2. **end-to-end closure of theorem dependencies** — handled by the isolated integration layer.

---

## 6. Current scope questions not yet finalized

### Loops

The current statement is loopless because `IsEven` counts `incidenceSet.ncard`, which counts a loop edge object once rather than degree contribution two.

Mathematically, singleton loops can be length-one cycles and included twice. Postpone the final convention decision until after the Port assembly:

- retain a loopless standard statement and add a pseudograph extension; or
- introduce loop-aware parity.

Do not claim “loops have no cover.”

### Finiteness

`[Finite α] [Finite β]` is an ambient-carrier convention. A later refinement may use active `V(G).Finite ∧ E(G).Finite`.

Do not start a genuinely edge-infinite CDC project in this engineering pass.

---

## 7. Immediate rule

Before editing any documentation or code, treat every earlier handoff saying “paper-only unconditional corollary” or “optional full integration” as superseded by this file.
