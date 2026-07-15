# 00 — READ FIRST: current AffineCDC architecture and status

**Date:** 2026-07-15  
**Status:** current public architecture entry point  
**Repository:** `Yuren-Tang/affine-cdc`

This file and the root `README.md` supersede earlier navigation, ledger, resume,
and mathematical-update documents wherever status or architecture conflicts.
Historical bodies remain in the repository for chronology only.

## 1. Approved natural theorem

The author-approved final theorem is:

> Every finite bridgeless multigraph has a cycle double cover.

“Finite” naturally means that the active edge set `E(G)` is finite. Loops are
allowed. The natural circuit is a nonempty inclusion-minimal cut-even edge set;
a singleton loop is therefore a circuit.

The loop reduction is explicit:

1. delete every loop;
2. prove CDC for the resulting loopless bridgeless core;
3. add two singleton circuit occurrences for each deleted loop.

This is **Path A**, and Path A has been approved.

## 2. Current Lean checkpoint is unchanged

Approval of Path A did not edit Lean.

The present `lean/AffineCDC/Statement.lean` still gives a loopless,
ambient-finite audit statement using the current vertex-incidence parity
convention. Its `CDCStatement` is defined but not proved.

Consequently:

- the approved full theorem is the final mathematical target;
- the current loopless statement is an implementation checkpoint;
- the exact Path A migration packet remains pending;
- the migration must not be described as already implemented or checked.

The exact future declaration names, signatures, compatibility lemmas, module
order, and audit migration have not been selected by this documentation task.

## 3. What is presently machine-checked

The current Lean repository verifies:

- local affine-family classification;
- quotient, gauge, dual, invariance, branching, and Fano machinery;
- the rank-three affine compatibility conclusion in the existing
  branching/cross-bit presentation;
- indexed dart-support construction with exact double coverage;
- the Graph-to-DartFlow port for the current loopless cubic representation;
- `cubic_flow_cdc`: a CDC corollary for an already cubic loopless graph carrying
  the required nowhere-zero `F₂³`-flow;
- finite even-support circuit decomposition in the current representation.

These are genuine checked results. They do not prove the full unconditional
finite bridgeless-multigraph theorem.

## 4. What remains unproved in Lean

- the Path A statement migration;
- active-edge finiteness and intrinsic cut-even circuit semantics;
- loop deletion and singleton-loop reinsertion;
- a named graph-level multiset even-double-cover layer in the approved
  architecture;
- cubic expansion and the required rank-three flow on the loopless core;
- the vertex-even/cut-even bridge at the required interfaces;
- pure cut-even collapse transport;
- the final end-to-end theorem.

## 5. Approved proof architecture

```text
finite bridgeless multigraph
→ delete loops
→ loopless bridgeless core
→ cubic expansion with rank-three binary flow
→ affine incidence compatibility
→ graph-level multiset even double cover
→ vertex-even/cut-even bridge on the loopless expansion
→ pure cut-even collapse transport
→ even double cover of the loopless original core
→ one final finite circuit decomposition
→ two singleton circuit occurrences for every removed loop
→ full finite bridgeless-multigraph CDC.
```

The graph-level multiset even double cover is the natural affine output. Empty
and repeated support occurrences are permitted. Circuit minimality is imposed
only by the one final decomposition after collapse.

`CubicFlowCDCStatement` and `cubic_flow_cdc` remain legitimate descriptions of
the current checked corollary. They are not the mandatory waist or the final
headline.

## 6. Hypothesis placement

- Looplessness is legitimate in the current Graph-to-DartFlow representation and
  in the current vertex-even/cut-even bridge.
- Looplessness is not an affine/Fano hypothesis and not an external theorem
  hypothesis.
- Connectedness is not required by affine compatibility.
- Pure cut-even collapse transport should not assume looplessness,
  connectedness, cubicity, a flow, affine data, or finite ambient carriers.
- Ambient `[Finite α] [Finite β]` describes the current checkpoint, not the
  natural final finiteness condition.

## 7. Independence and proof-path rule

No external CDC formalization controls this project. It may be studied for
literature or provenance, but it does not determine this project's statement,
encoding, architecture, or implementation.

The final theorem must be proved through the AffineCDC chain. Directly invoking
another formalization's complete CDC endpoint is not an acceptable substitute.

## 8. Documentation authority

For current public status use, in order:

1. the root `README.md`;
2. this file;
3. actual Lean source for the exact present implementation;
4. historical files only for chronology.

The following files are retained but superseded as active guidance:

- `navigation-2026-07-14.md`;
- `ledger.md`;
- `01_ENGINEERING_RESUME_PLAN.md`;
- `02_MATHEMATICAL_UPDATE.md`.

Their old bodies may contain true historical facts or still-interesting
mathematics, but their endpoint, loop, finiteness, integration, and work-order
claims do not override this entry point.
