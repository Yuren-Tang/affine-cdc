import AffineCDC.Cycle
import AffineCDC.Decompose

/-!
# Bridge to Mathlib graphs (the Port)

Proves `CDCStatement` (Statement.lean) from the affine development's endpoint
`DartFlow.exists_cycle_double_cover`.  The work is a bridge in two directions:

* **Graph → DartFlow**: a finite loopless cubic multigraph with a nowhere-zero
  `𝔽₂³`-flow yields a `DartFlow`; the three flow values at each vertex are
  distinct, nonzero and sum to zero, hence form the Klein triple of a plane
  (`vertexPlane`), and the incident edges biject with its directions.
* **cover → cycles**: the even 2-regular support subgraphs produced by the
  construction are decomposed into genuine cycles by `exists_cycle_decomposition`.

This file may use the internal vocabulary freely; the audit surface is
`Statement.lean`, which does not.
-/

namespace AffineCDC.Port

open Graph AffineCDC.Statement

/-- The flow space `𝔽₂³`. -/
abbrev Γ : Type := Fin 3 → ZMod 2

variable {α β : Type*} [Finite α] [Finite β] {G : Graph α β}
  {f : β → Γ}

/-! ## The three incident edges and their Klein structure -/

/-- At a vertex of a cubic graph, the incident edge set has three distinct
elements whose flow values are nonzero and sum to zero. -/
lemma exists_incident_triple (hcubic : Cubic G) (hflow : NowhereZeroFlow G f)
    {u : α} (hu : u ∈ V(G)) :
    ∃ e₁ e₂ e₃ : β, e₁ ≠ e₂ ∧ e₁ ≠ e₃ ∧ e₂ ≠ e₃ ∧
      G.incidenceSet u = {e₁, e₂, e₃} ∧
      f e₁ ≠ 0 ∧ f e₂ ≠ 0 ∧ f e₃ ≠ 0 ∧
      f e₁ + f e₂ + f e₃ = 0 := by
  obtain ⟨e₁, e₂, e₃, h12, h13, h23, hset⟩ :=
    Set.ncard_eq_three.mp (hcubic u hu)
  have hinc : ∀ e ∈ G.incidenceSet u, e ∈ E(G) :=
    fun e he => (show G.Inc e u from he).edge_mem
  have hmem : ∀ e ∈ ({e₁, e₂, e₃} : Set β), e ∈ E(G) := hset ▸ hinc
  have hz : ∀ e ∈ ({e₁, e₂, e₃} : Set β), f e ≠ 0 := fun e he =>
    hflow.nowhere_zero e (hmem e he)
  refine ⟨e₁, e₂, e₃, h12, h13, h23, hset,
    hz e₁ (by simp), hz e₂ (by simp), hz e₃ (by simp), ?_⟩
  have hcons := hflow.conservation u hu
  rw [hset] at hcons
  rw [finsum_mem_insert f (by simp [h12, h13]) (Set.toFinite _),
    finsum_mem_insert f (by simp [h23]) (Set.toFinite _),
    finsum_mem_singleton] at hcons
  rw [← hcons]
  abel

/-- The plane at a vertex: the span of the incident flow values. -/
noncomputable def vertexPlane (G : Graph α β) (f : β → Γ) (u : α) :
    Submodule (ZMod 2) Γ :=
  Submodule.span (ZMod 2) (f '' G.incidenceSet u)

/-- The incident flow values lie in the vertex plane. -/
lemma mem_vertexPlane {u : α} {e : β} (he : G.Inc e u) :
    f e ∈ vertexPlane G f u :=
  Submodule.subset_span ⟨e, he, rfl⟩

/-- At an actual vertex of a cubic graph with a nowhere-zero flow, the vertex
plane is a plane (its three incident values form a Klein triple). -/
lemma isPlane_vertexPlane (hcubic : Cubic G) (hflow : NowhereZeroFlow G f)
    {u : α} (hu : u ∈ V(G)) : IsPlane (vertexPlane G f u) := by
  obtain ⟨e₁, e₂, e₃, h12, h13, h23, hset, hz1, hz2, hz3, hsum⟩ :=
    exists_incident_triple hcubic hflow hu
  set a := f e₁ with ha; set b := f e₂ with hb; set c := f e₃ with hc
  -- `c = a + b`, and `a ≠ b` (else `c = 0`)
  have hc_eq : c = a + b := (char2_add_eq_zero_iff.mp hsum).symm
  have hab : a ≠ b := fun h => hz3 (by rw [hc_eq, h, char2_add_self])
  -- the plane equals span {a, b}
  have himg : f '' G.incidenceSet u = {a, b, c} := by
    rw [hset, Set.image_insert_eq, Set.image_insert_eq, Set.image_singleton]
  have hspan : vertexPlane G f u = Submodule.span (ZMod 2) {a, b} := by
    rw [vertexPlane, himg]
    have hcmem : c ∈ Submodule.span (ZMod 2) ({a, b} : Set Γ) := by
      rw [hc_eq]
      exact Submodule.add_mem _ (Submodule.subset_span (by simp))
        (Submodule.subset_span (by simp))
    have hins : ({a, b, c} : Set Γ) = insert c {a, b} := by
      ext x; simp; tauto
    rw [hins, Submodule.span_insert_eq_span hcmem]
  -- span {a, b} has finrank two
  apply IsPlane.of_finrank_eq_two
  rw [hspan]
  have hli : LinearIndependent (ZMod 2) ![a, b] := by
    rw [linearIndependent_fin2]
    refine ⟨by simpa using hz2, fun s => ?_⟩
    simp only [Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_zero]
    have h01 : s = 0 ∨ s = 1 := by revert s; decide
    rcases h01 with rfl | rfl
    · rw [zero_smul]; exact fun h => hz1 h.symm
    · rw [one_smul]; exact fun h => hab h.symm
  have hrange : (Set.range ![a, b]) = {a, b} := by
    ext x
    simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨i, rfl⟩; fin_cases i <;> simp
    · rintro (rfl | rfl)
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
  have hfr := finrank_span_eq_card hli
  rw [hrange] at hfr
  rw [hfr]; simp

end AffineCDC.Port
