# 01 — Engineering resume plan for Opus

**Base commit:** `596d488f3c448c385ad361f57df1532030a9f140`

---

## 1. Verified repository state at pause

Completed:

- T1–T7 and Fano compatibility;
- `DartFlow.exists_gluing`;
- `DartFlow.exists_cycle_double_cover`;
- `Cover.lean` and `Cycle.lean`;
- Mathlib-only unconditional `Statement.CDCStatement`;
- `Decompose.lean`: finite even edge-set → multiset of minimal even circuits;
- `Port.lean` Graph → DartFlow bridge:
  - `exists_incident_triple`;
  - `vertexPlane`;
  - `vertex_facts`;
  - complete `graphDartFlow`.

The latest Graph→DartFlow commit explicitly described the remaining work as cover assembly and the final CDC theorem.

No newer visible commit exists after the Statement scope correction.

---

## 2. Phase P1 — finish the macro Port

Complete the intermediate Graph-language theorem. A descriptive theorem name may be clearer than promoting a standalone proposition:

```lean
theorem cycleDoubleCover_of_cubic_of_nowhereZeroFlow
    ...
    : ∃ 𝒞, IsCycleDoubleCover G 𝒞
```

The current name `cubic_flow_cdc : CubicFlowCDCStatement` is acceptable if its documentation says **intermediate only**.

### Required assembly

Starting from:

```lean
D := graphDartFlow hloop hcubic hflow
D.exists_cycle_double_cover
```

perform:

1. project every sigma-closed dart support to an edge support;
2. prove edge membership is equivalent to membership of either endpoint dart;
3. prove each projected support is `Statement.IsEven`;
4. use `exists_cycle_decomposition` on each finite even support;
5. flatten/bind the Γ-indexed multisets of circuits;
6. prove every resulting member satisfies `IsCycle`;
7. transfer exact-two dart coverage to exact-two graph-edge multiplicity;
8. package the intermediate theorem;
9. add:
   ```lean
   #check ...
   #print axioms ...
   ```

Do not alter the affine/Fano core to make this bookkeeping easier unless a genuinely missing API is identified.

---

## 3. Phase P2 — isolated unconditional integration

After P1, create or resume a separate integration package.

### Dependency policy

- AffineCDC core keeps its present Mathlib pin and no cdc-lean dependency.
- The integration package has its own `lakefile`.
- Resolve the pin mismatch inside the integration package.
- Do not change the core pin merely to make the integration convenient.

### Mathematical path

Reuse the already formalized outer infrastructure:

```text
finite loopless bridgeless multigraph
→ cubic expansion / reduction
→ Jaeger–Kilpatrick or equivalent F₂³-flow input
→ AffineCDC intermediate cubic-flow theorem
→ transport/projection through the reduction
→ standard cycle double cover
```

Final declaration:

```lean
theorem cycle_double_cover :
  AffineCDC.Statement.CDCStatement := by
  ...
```

### Proof-path integrity

The final theorem must demonstrably depend on the AffineCDC cover construction.

Provide:

- a short declaration dependency map;
- source pointers to the call into the AffineCDC Port theorem;
- confirmation that the old complete CDC endpoint is not invoked.

---

## 4. Phase P3 — final Statement audit

Only after the theorem chain closes, revisit:

1. loops convention;
2. finite ambient carriers vs active finite graph;
3. universe/generalization details;
4. misleading comments such as “loops trivially have no cover.”

Any Statement change must be accompanied by adapting the final theorem type, not by weakening the theorem target to a cubic/flow proposition.

---

## 5. Documentation repair

Update `docs/ledger.md`, `docs/HANDOFF.md`, README and architecture map so they say consistently:

- AffineCDC core is self-contained;
- CDC extraction is in core scope;
- the Graph cubic-flow theorem is an intermediate Port;
- the overall project final theorem is unconditional `CDCStatement`;
- the full composition lives in an isolated integration package;
- T1 is the mathematical basis of comparison;
- `slotFamily_eq_localFamily` is a worked example/dictionary;
- no release/tag/DOI before user review.

Explicitly mark the previously archived wrong navigation document as superseded.

---

## 6. Stop conditions

Pause and report rather than silently changing scope if:

- the external outer reduction cannot be reused without calling the old final theorem;
- the integration pin conflict would require changing the core;
- the Statement convention makes a transport theorem false;
- the Port assembly exposes a real gap in `DartFlow.exists_cycle_double_cover`.

Do not solve a scope problem by weakening the final target.
