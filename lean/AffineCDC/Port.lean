import AffineCDC.Cycle
import AffineCDC.Decompose

/-!
# The cubic-flow interface (the Port)

This file proves the **intermediate** result — *cubic + nowhere-zero `𝔽₂³`-flow
⟹ cycle double cover* — by constructing the affine core's `DartFlow` from a
Mathlib multigraph and reading off the cover.  It is **not** the CDC statement
(`Statement.lean`, which is the standard unconditional conjecture with no
cubic/flow hypotheses); it is the semantic port from Mathlib's `Graph α β` to
the affine development.  The full unconditional CDC composes this construction
with the classical bridgeless→cubic→8-flow reduction.

The work is a bridge in two directions:

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

/-! ## Proof-interface notions (cubic graphs and flows)

These are **not** part of the CDC statement (`Statement.lean`); they are the
hypotheses of the affine construction, kept here in the construction layer. -/

/-- `G` is **cubic** if every vertex is incident to exactly three edges. -/
def Cubic (G : Graph α β) : Prop := ∀ x ∈ V(G), (G.incidenceSet x).ncard = 3

/-- A **nowhere-zero `𝔽₂³`-flow**: nonzero values on the edges summing to zero
around every vertex.  Over characteristic two, orientation is irrelevant
(`-x = x`), so conservation is the unoriented incidence sum. -/
structure NowhereZeroFlow (G : Graph α β) (f : β → Γ) : Prop where
  nowhere_zero : ∀ e ∈ E(G), f e ≠ 0
  conservation : ∀ x ∈ V(G), ∑ᶠ e ∈ G.incidenceSet x, f e = 0

/-- The **intermediate** (cubic-flow) statement: every finite loopless cubic
multigraph carrying a nowhere-zero `𝔽₂³`-flow has a cycle double cover.  This is
the semantic port that the affine core establishes; the unconditional CDC
(`Statement.CDCStatement`) is obtained by prepending the classical
bridgeless→cubic→8-flow reduction. -/
def CubicFlowCDCStatement : Prop :=
  ∀ {α β : Type} [Finite α] [Finite β] (G : Graph α β) (f : β → Γ),
    Loopless G → Cubic G → NowhereZeroFlow G f →
    ∃ 𝒞 : Multiset (Set β), IsCycleDoubleCover G 𝒞

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

/-- Packaged facts at a vertex: the three incident edges, their nonzero and
pairwise-distinct values, and the characterization of the plane's elements as
`{0, f e₁, f e₂, f e₃}`.  Everything the `DartFlow` construction consumes. -/
lemma vertex_facts (hcubic : Cubic G) (hflow : NowhereZeroFlow G f)
    {u : α} (hu : u ∈ V(G)) :
    ∃ e₁ e₂ e₃ : β,
      (∀ e, G.Inc e u ↔ e = e₁ ∨ e = e₂ ∨ e = e₃) ∧
      f e₁ ≠ 0 ∧ f e₂ ≠ 0 ∧ f e₃ ≠ 0 ∧
      f e₁ ≠ f e₂ ∧ f e₁ ≠ f e₃ ∧ f e₂ ≠ f e₃ ∧
      (∀ h ∈ vertexPlane G f u, h = 0 ∨ h = f e₁ ∨ h = f e₂ ∨ h = f e₃) := by
  obtain ⟨e₁, e₂, e₃, h12, h13, h23, hset, hz1, hz2, hz3, hsum⟩ :=
    exists_incident_triple hcubic hflow hu
  set a := f e₁ with ha; set b := f e₂ with hb; set c := f e₃ with hc
  have hc_eq : c = a + b := (char2_add_eq_zero_iff.mp hsum).symm
  have hab : a ≠ b := fun h => hz3 (by rw [hc_eq, h, char2_add_self])
  have hbc : b ≠ c := by
    rw [hc_eq]; intro hbe
    exact hz1 (add_right_cancel (b := b)
      (show a + b = 0 + b by rw [zero_add]; exact hbe.symm))
  have hac : a ≠ c := by
    rw [hc_eq]; intro hae
    exact hz2 (add_left_cancel
      (show a + 0 = a + b by rw [add_zero]; exact hae)).symm
  -- incidence characterization
  have hincs : ∀ e, G.Inc e u ↔ e = e₁ ∨ e = e₂ ∨ e = e₃ := by
    intro e
    rw [show G.Inc e u ↔ e ∈ G.incidenceSet u from Iff.rfl, hset]
    simp [Set.mem_insert_iff]
  -- plane = span {a, b}; enumerate its elements
  have hspan : vertexPlane G f u = Submodule.span (ZMod 2) {a, b} := by
    have himg : f '' G.incidenceSet u = {a, b, c} := by
      rw [hset, Set.image_insert_eq, Set.image_insert_eq, Set.image_singleton]
    rw [vertexPlane, himg]
    have hcmem : c ∈ Submodule.span (ZMod 2) ({a, b} : Set Γ) := by
      rw [hc_eq]
      exact Submodule.add_mem _ (Submodule.subset_span (by simp))
        (Submodule.subset_span (by simp))
    have hins : ({a, b, c} : Set Γ) = insert c {a, b} := by ext x; simp; tauto
    rw [hins, Submodule.span_insert_eq_span hcmem]
  have hcarrier : ∀ h ∈ vertexPlane G f u, h = 0 ∨ h = a ∨ h = b ∨ h = c := by
    intro h hh
    rw [hspan, Submodule.mem_span_pair] at hh
    obtain ⟨s, t, hst⟩ := hh
    have z01 : ∀ r : ZMod 2, r = 0 ∨ r = 1 := by decide
    rcases z01 s with rfl | rfl <;> rcases z01 t with rfl | rfl <;>
      simp only [zero_smul, one_smul, zero_add, add_zero] at hst
    · exact Or.inl hst.symm
    · exact Or.inr (Or.inr (Or.inl hst.symm))
    · exact Or.inr (Or.inl hst.symm)
    · exact Or.inr (Or.inr (Or.inr (by rw [hc_eq]; exact hst.symm)))
  exact ⟨e₁, e₂, e₃, hincs, hz1, hz2, hz3, hab, hac, hbc, hcarrier⟩

/-! ## The DartFlow of a graph -/

/-- Vertices of the DartFlow: the actual vertex set (so every one carries a
plane). -/
abbrev Vtx (G : Graph α β) : Type _ := {x : α // x ∈ V(G)}

/-- Darts: incidence pairs `(edge, incident vertex)`. -/
abbrev Dartt (G : Graph α β) : Type _ := {p : β × α // G.Inc p.1 p.2}

/-- The other end of a dart's edge (the `σ`-partner's vertex is well defined by
`right_unique`). -/
lemma other_other (d : Dartt G) : (d.2.inc_other).other = d.1.2 :=
  ((d.2.inc_other).isLink_other).right_unique (d.2.isLink_other.symm)

variable (hloop : Loopless G) (hcubic : Cubic G) (hflow : NowhereZeroFlow G f)

/-- The DartFlow associated to a finite loopless cubic graph with a
nowhere-zero `𝔽₂³`-flow. -/
noncomputable def graphDartFlow : DartFlow (Dartt G) (Vtx G) Γ where
  σ d := ⟨(d.1.1, d.2.other), d.2.inc_other⟩
  invol d := by
    apply Subtype.ext; apply Prod.ext
    · rfl
    · exact other_other d
  no_fix d := by
    intro h
    have hv : (d.2.other) = d.1.2 := congrArg (fun p => p.1.2) h
    exact hloop d.1.1 d.1.2 (by
      have := d.2.isLink_other; rw [hv] at this; exact this)
  vtx d := ⟨d.1.2, d.2.isLink_other.left_mem⟩
  f d := f d.1.1
  f_σ _ := rfl
  W u := vertexPlane G f u.1
  plane u := isPlane_vertexPlane hcubic hflow u.2
  mem d := mem_vertexPlane d.2
  nz d := hflow.nowhere_zero d.1.1 d.2.edge_mem
  cubic u := by
    obtain ⟨e₁, e₂, e₃, hincs, hz1, hz2, hz3, h12, h13, h23, hcarrier⟩ :=
      vertex_facts hcubic hflow u.2
    constructor
    · -- injective
      intro d d' heq
      have hff : f d.1.1.1 = f d'.1.1.1 := congrArg Subtype.val heq
      have hdu : d.1.1.2 = u.1 := congrArg Subtype.val d.2
      have hdu' : d'.1.1.2 = u.1 := congrArg Subtype.val d'.2
      have hince : d.1.1.1 = e₁ ∨ d.1.1.1 = e₂ ∨ d.1.1.1 = e₃ :=
        (hincs _).mp (hdu ▸ d.1.2)
      have hince' : d'.1.1.1 = e₁ ∨ d'.1.1.1 = e₂ ∨ d'.1.1.1 = e₃ :=
        (hincs _).mp (hdu' ▸ d'.1.2)
      have hedge : d.1.1.1 = d'.1.1.1 := by
        rcases hince with h | h | h <;> rcases hince' with h' | h' | h' <;>
          rw [h, h'] at hff ⊢ <;>
          first
            | rfl
            | exact absurd hff h12 | exact absurd hff h13 | exact absurd hff h23
            | exact absurd hff.symm h12 | exact absurd hff.symm h13
            | exact absurd hff.symm h23
      apply Subtype.ext; apply Subtype.ext; apply Prod.ext hedge
      exact hdu.trans hdu'.symm
    · -- surjective
      rintro ⟨h, hmem, hne⟩
      rcases hcarrier h hmem with h0 | h1 | h2 | h3
      · exact absurd h0 hne
      · exact ⟨⟨⟨(e₁, u.1), (hincs e₁).mpr (Or.inl rfl)⟩, Subtype.ext rfl⟩,
          Subtype.ext h1.symm⟩
      · exact ⟨⟨⟨(e₂, u.1), (hincs e₂).mpr (Or.inr (Or.inl rfl))⟩, Subtype.ext rfl⟩,
          Subtype.ext h2.symm⟩
      · exact ⟨⟨⟨(e₃, u.1), (hincs e₃).mpr (Or.inr (Or.inr rfl))⟩, Subtype.ext rfl⟩,
          Subtype.ext h3.symm⟩

/-! ## The cover assembly (P1): `cubic_flow_cdc` -/

open scoped Classical in
/-- Filtering-card is additive over a `Finset.sum` of multisets. -/
private lemma card_filter_sum {γ : Type*} {ι : Type*} (T : Finset ι)
    (g : ι → Multiset (Set γ)) (p : Set γ → Prop) :
    ((T.sum g).filter p).card = T.sum (fun i => ((g i).filter p).card) := by
  classical
  induction T using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Multiset.filter_add, Multiset.card_add,
      Finset.sum_insert ha, ih]

/-- Membership in a `Finset.sum` of multisets. -/
private lemma mem_finset_sum {γ : Type*} {ι : Type*} (T : Finset ι)
    (g : ι → Multiset (Set γ)) (C : Set γ) :
    C ∈ T.sum g ↔ ∃ i ∈ T, C ∈ g i := by
  classical
  induction T using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Multiset.mem_add, ih, Finset.exists_mem_insert]

/-- **Intermediate macro-Port theorem** (`cubic_flow_cdc`): every finite
loopless cubic multigraph carrying a nowhere-zero `𝔽₂³`-flow has a cycle
double cover.  Proved entirely within the AffineCDC core (no `cdc-lean`).
This is *not* the final unconditional CDC; the unconditional theorem is
obtained in an isolated integration layer composing the classical
bridgeless→cubic→flow reduction with this construction. -/
theorem cubic_flow_cdc : CubicFlowCDCStatement := by
  intro α β _ _ G f hloop hcubic hflow
  classical
  letI : Fintype (Dartt G) := Fintype.ofFinite _
  letI : Fintype (Vtx G) := Fintype.ofFinite _
  set D := graphDartFlow hloop hcubic hflow with hD
  -- codimension-one at every vertex plane
  have hcodim : ∀ u : Vtx G, Module.finrank (ZMod 2) (Γ ⧸ D.W u) = 1 := by
    intro u
    have hΓ : Module.finrank (ZMod 2) Γ = 3 := by simp [Γ]
    have hW : Module.finrank (ZMod 2) (D.W u) = 2 :=
      (isPlane_vertexPlane hcubic hflow u.2).finrank_eq_two
    have hq := Submodule.finrank_quotient_add_finrank (D.W u)
    omega
  obtain ⟨M, hσ, hcov2, huniq, -⟩ := D.exists_indexed_dart_cover hcodim
  -- edge supports
  set edgeSupp : Γ → Set β := fun s => (fun d : Dartt G => d.1.1) '' M s with hES
  -- (2) edge membership ⟺ endpoint-dart membership
  have hEdart : ∀ (s : Γ) (e : β) (u : α) (he : G.Inc e u),
      e ∈ edgeSupp s ↔ (⟨(e, u), he⟩ : Dartt G) ∈ M s := by
    intro s e u he
    constructor
    · rintro ⟨d, hd, hde⟩
      have hincd : G.Inc e d.1.2 := hde ▸ d.2
      rcases hincd.isLink_other.left_eq_or_eq he.isLink_other with hw | hw
      · have hdeq : d = ⟨(e, u), he⟩ := by
          apply Subtype.ext; exact Prod.ext hde hw
        rwa [hdeq] at hd
      · have hdeq : d = D.σ ⟨(e, u), he⟩ := by
          apply Subtype.ext; exact Prod.ext hde hw
        rw [hdeq] at hd
        exact (hσ s ⟨(e, u), he⟩).mp hd
    · intro hmem
      exact ⟨⟨(e, u), he⟩, hmem, rfl⟩
  -- edge supports lie in the edge set
  have hESE : ∀ s, edgeSupp s ⊆ E(G) := by
    rintro s e ⟨d, hd, rfl⟩; exact d.2.edge_mem
  -- (4-prep) support darts at a vertex are even in number
  have hSu_even : ∀ (s : Γ) (u : α),
      Even ({d : Dartt G | d ∈ M s ∧ d.1.2 = u}.ncard) := by
    intro s u
    by_cases hne : {d : Dartt G | d ∈ M s ∧ d.1.2 = u}.Nonempty
    · obtain ⟨d, hd, hdu⟩ := hne
      obtain ⟨d', ⟨hd'ne, hd'v, hd'm⟩, hd'uniq⟩ := huniq s d hd
      have hd'u : d'.1.2 = u := by
        have hv : d'.1.2 = d.1.2 := congrArg Subtype.val hd'v
        rw [hv]; exact hdu
      have hSeq : {d : Dartt G | d ∈ M s ∧ d.1.2 = u} = {d, d'} := by
        ext x
        simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
        constructor
        · rintro ⟨hxm, hxu⟩
          by_cases hxd : x = d
          · exact Or.inl hxd
          · refine Or.inr (hd'uniq x ⟨hxd, ?_, hxm⟩)
            apply Subtype.ext
            show x.1.2 = d.1.2
            rw [hxu, hdu]
        · rintro (rfl | rfl)
          · exact ⟨hd, hdu⟩
          · exact ⟨hd'm, hd'u⟩
      rw [hSeq, Set.ncard_pair (Ne.symm hd'ne)]
      exact even_two
    · rw [Set.not_nonempty_iff_eq_empty] at hne
      rw [hne, Set.ncard_empty]; exact ⟨0, rfl⟩
  -- (3) each edge support is even
  have hEven : ∀ s, Statement.IsEven G (edgeSupp s) := by
    intro s u
    have hset : edgeSupp s ∩ G.incidenceSet u
        = (fun d : Dartt G => d.1.1) '' {d : Dartt G | d ∈ M s ∧ d.1.2 = u} := by
      ext e
      simp only [Set.mem_inter_iff, Set.mem_image, Set.mem_setOf_eq]
      constructor
      · rintro ⟨hes, hinc⟩
        exact ⟨⟨(e, u), hinc⟩, ⟨(hEdart s e u hinc).mp hes, rfl⟩, rfl⟩
      · rintro ⟨d, ⟨hdm, hdu⟩, rfl⟩
        exact ⟨⟨d, hdm, rfl⟩, hdu ▸ d.2⟩
    rw [hset]
    have hinj : Set.InjOn (fun d : Dartt G => d.1.1)
        {d : Dartt G | d ∈ M s ∧ d.1.2 = u} := by
      rintro d1 ⟨_, hd1u⟩ d2 ⟨_, hd2u⟩ h12
      apply Subtype.ext; exact Prod.ext h12 (by rw [hd1u, hd2u])
    rw [hinj.ncard_image]
    exact hSu_even s u
  -- (7) each edge lies in exactly two edge supports
  have hEdgeCov : ∀ e ∈ E(G), {s : Γ | e ∈ edgeSupp s}.ncard = 2 := by
    intro e he
    obtain ⟨u, v, huv⟩ := G.exists_isLink_of_mem_edgeSet he
    have hincu : G.Inc e u := ⟨v, huv⟩
    have hEq : {s : Γ | e ∈ edgeSupp s} = {s | (⟨(e, u), hincu⟩ : Dartt G) ∈ M s} := by
      ext s; exact hEdart s e u hincu
    rw [hEq]; exact hcov2 _
  -- (4,5) decompose each support into cycles
  have hdecomp : ∀ s, ∃ 𝒟 : Multiset (Set β),
      (∀ C ∈ 𝒟, Statement.IsCycle G C) ∧
      ∀ e, (𝒟.filter fun C => e ∈ C).card = if e ∈ edgeSupp s then 1 else 0 :=
    fun s => Statement.exists_cycle_decomposition' G (hESE s) (hEven s)
  choose 𝒟 h𝒟cyc h𝒟count using hdecomp
  -- (6,7,8) bind over `Γ` and count
  refine ⟨Finset.univ.sum 𝒟, ?_, ?_⟩
  · intro C hC
    rw [mem_finset_sum] at hC
    obtain ⟨s, -, hCs⟩ := hC
    exact h𝒟cyc s C hCs
  · intro e he
    rw [card_filter_sum, Finset.sum_congr rfl (fun s _ => h𝒟count s e),
      Finset.sum_boole]
    have h1 : {s : Γ | e ∈ edgeSupp s}.ncard = 2 := hEdgeCov e he
    rw [Set.ncard_eq_toFinset_card', Set.toFinset_setOf] at h1
    exact_mod_cast h1

end AffineCDC.Port
