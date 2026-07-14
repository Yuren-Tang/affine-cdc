import Mathlib

/-!
# A self-contained statement of the Cycle Double Cover theorem

**This file is the audit surface.**  It imports only Mathlib and uses none of
the vocabulary of the `AffineCDC` development.  A graph theorist can read it in
isolation and confirm that `CDCStatement` really is the Cycle Double Cover
conjecture (for the case we prove), with no reliance on bespoke definitions.

The graph object is Mathlib's multigraph `Graph α β`
(`Mathlib/Combinatorics/Graph/Basic.lean`): a vertex set `V(G) : Set α`, an
edge set `E(G) : Set β`, and an incidence predicate `G.IsLink e x y`.  Parallel
edges are permitted (distinct `e, e' : β` with the same ends), as the
conjecture requires; `SimpleGraph` would be too restrictive.

Everything else — even edge-sets, cycles, the double cover, cubicity and
nowhere-zero flows — is defined **here**, from first principles, in a handful
of lines.

## Scope

We state the theorem in the form actually established by this development:

> Every finite loopless cubic multigraph carrying a nowhere-zero `𝔽₂³`-flow
> has a cycle double cover.

This is the mathematical core of the conjecture (OpenAI's Lemmas 2.1–2.2).
Upgrading it to *every finite bridgeless graph* uses two classical, cited
inputs that this development does **not** re-prove and that are visibly absent
from the statement below:

* the Jaeger–Kilpatrick / Tutte theorem that every bridgeless graph admits a
  nowhere-zero `8`-flow (equivalently a nowhere-zero `𝔽₂³`-flow), and
* the standard reduction of the conjecture to cubic graphs.

Keeping them out of `CDCStatement` is deliberate: the statement claims exactly
what is proved, and no more.
-/

namespace AffineCDC.Statement

open Graph
open scoped Classical

variable {α β : Type*}

/-- The **cycle** notion, following the standard matroid-circuit definition:
a nonempty even edge-set that is minimal for inclusion.  An edge-set is *even*
when every vertex meets an even number of its edges; a minimal nonempty even
set is exactly a single circuit (cycle) of the multigraph.  This is
connectivity-free and matches the definition used in the OpenAI formalization. -/
def IsEven (G : Graph α β) (C : Set β) : Prop :=
  ∀ x : α, Even (C ∩ G.incidenceSet x).ncard

/-- A **cycle** (circuit): a minimal nonempty even edge-set. -/
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

/-- `G` is **loopless** if no edge joins a vertex to itself. -/
def Loopless (G : Graph α β) : Prop := ∀ e x, ¬ G.IsLink e x x

/-- `G` is **cubic** if every vertex is incident to exactly three edges. -/
def Cubic (G : Graph α β) : Prop := ∀ x ∈ V(G), (G.incidenceSet x).ncard = 3

/-- A **nowhere-zero `𝔽₂³`-flow**: an assignment of nonzero values in
`𝔽₂³ = (Fin 3 → ZMod 2)` to the edges whose values sum to zero around every
vertex.  Over characteristic two, orientation is irrelevant (`-x = x`), so the
conservation law is the unoriented incidence sum. -/
structure NowhereZeroFlow (G : Graph α β) (f : β → (Fin 3 → ZMod 2)) : Prop where
  nowhere_zero : ∀ e ∈ E(G), f e ≠ 0
  conservation : ∀ x ∈ V(G), ∑ᶠ e ∈ G.incidenceSet x, f e = 0

/-- **The Cycle Double Cover theorem** (the case proved by this development):
every finite loopless cubic multigraph with a nowhere-zero `𝔽₂³`-flow has a
cycle double cover.

`α`, `β` range over finite ambient types, so `G` is a finite multigraph. -/
def CDCStatement : Prop :=
  ∀ {α β : Type} [Finite α] [Finite β] (G : Graph α β),
    Loopless G → Cubic G → (∃ f, NowhereZeroFlow G f) →
    ∃ 𝒞 : Multiset (Set β), IsCycleDoubleCover G 𝒞

end AffineCDC.Statement
