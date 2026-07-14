import Mathlib

/-!
# A self-contained statement of the Cycle Double Cover conjecture

**This file is the audit surface.**  It imports only Mathlib and contains only
the standard vocabulary of the conjecture.  A graph theorist can read it in
isolation and confirm that `CDCStatement` is *exactly* the Cycle Double Cover
conjecture — every finite loopless bridgeless multigraph has a cycle double
cover — with no reliance on bespoke definitions and no extra hypotheses.

In particular the audit surface contains **no** proof-interface notions
(no cubic, no flows, no `𝔽₂³`, no darts, no planes); those belong to the
construction (`Port.lean`), not the statement.

The graph object is Mathlib's multigraph `Graph α β`
(`Mathlib/Combinatorics/Graph/Basic.lean`): a vertex set `V(G) : Set α`, an
edge set `E(G) : Set β`, and an incidence predicate `G.IsLink e x y`.  Parallel
edges are permitted (distinct `e, e' : β` with the same ends), as the
conjecture requires; `SimpleGraph` would be too restrictive.
-/

namespace AffineCDC.Statement

open Graph
open scoped Classical

variable {α β : Type*}

/-! ## Cycles and covers -/

/-- An edge-set is **even** when every vertex meets an even number of its edges
(even degree).  For a loopless graph the incidence count is the degree. -/
def IsEven (G : Graph α β) (C : Set β) : Prop :=
  ∀ x : α, Even (C ∩ G.incidenceSet x).ncard

/-- A **cycle** (circuit), in the standard matroid-circuit sense: a minimal
nonempty even edge-set.  A minimal nonempty even set is exactly a single
circuit of the multigraph; this is connectivity-free. -/
structure IsCycle (G : Graph α β) (C : Set β) : Prop where
  nonempty : C.Nonempty
  subset : C ⊆ E(G)
  even : IsEven G C
  minimal : ∀ D : Set β, D.Nonempty → D ⊆ C → IsEven G D → D = C

/-- A **cycle double cover**: a multiset of cycles in which every edge of the
graph occurs in exactly two members (counted with multiplicity). -/
structure IsCycleDoubleCover (G : Graph α β) (𝒞 : Multiset (Set β)) : Prop where
  isCycle : ∀ C ∈ 𝒞, IsCycle G C
  coveredTwice : ∀ e ∈ E(G), (𝒞.filter fun C => e ∈ C).card = 2

/-! ## Loopless and bridgeless -/

/-- `G` is **loopless** if no edge joins a vertex to itself. -/
def Loopless (G : Graph α β) : Prop := ∀ e x, ¬ G.IsLink e x x

/-- The edge `e` **crosses the cut** determined by the vertex subset `S` if its
two ends lie on opposite sides of `S`. -/
def CrossesCut (G : Graph α β) (S : Set α) (e : β) : Prop :=
  ∃ x y, G.IsLink e x y ∧ ((x ∈ S) ≠ (y ∈ S))

/-- The **cut** of a vertex subset `S`: the set of edges crossing it. -/
def cutSet (G : Graph α β) (S : Set α) : Set β :=
  {e | CrossesCut G S e}

/-- `G` is **bridgeless** if no cut consists of a single edge.  (An edge that is
the sole member of some cut is a bridge; equivalently, its removal increases
the number of connected components.  This is the standard cut characterization,
matching the definition used in the OpenAI formalization.) -/
def Bridgeless (G : Graph α β) : Prop :=
  ∀ S : Set α, (cutSet G S).ncard ≠ 1

/-! ## The conjecture -/

/-- **The Cycle Double Cover conjecture.**  Every finite loopless bridgeless
multigraph has a cycle double cover.

`α`, `β` range over finite ambient types, so `G` is a finite multigraph.  There
are **no** additional hypotheses: `Loopless` and `Bridgeless` are the standard
scope of the conjecture (loops trivially have no cover; a bridge lies in no
cycle). -/
def CDCStatement : Prop :=
  ∀ {α β : Type} [Finite α] [Finite β] (G : Graph α β),
    Loopless G → Bridgeless G →
    ∃ 𝒞 : Multiset (Set β), IsCycleDoubleCover G 𝒞

end AffineCDC.Statement
