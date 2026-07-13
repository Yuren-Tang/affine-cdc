import AffineCDC.Cover

/-!
# The double cover (G, part 2: partners, rotation, the cover)

* `dart_eq_of_f_eq`: at a fixed vertex, darts are determined by their flow
  values (injectivity half of `cubic`);
* `partnerD` (**G1**): for `d` in the support of `s`, the *other* support
  dart at the same vertex — with the explicit value formula
  `f(partner) = (s + m_u) + f d` (no choice: the third point of the plane);
  `Msupp_vertex_unique` is the exactly-two vertex condition;
* `rho`/`rhoInv` (**G2**): the rotation `ρ = partner ∘ σ` and its inverse
  `σ ∘ partner`; its orbits are the cycles of the support — in dart
  language, cycle decomposition *is* orbit decomposition of a permutation;
* `exists_cycle_double_cover` (**G4**): the endpoint — supports of a glued
  gauge form a cycle double cover: σ-closed subgraphs covering every edge
  exactly twice, 2-regular where present, with the rotation witnessing the
  cycle structure.
-/

namespace AffineCDC

namespace DartFlow

variable {Δ V Γ : Type*} [AddCommGroup Γ] [Module (ZMod 2) Γ]
variable (D : DartFlow Δ V Γ)

/-- At a fixed vertex, a dart is determined by its flow value. -/
lemma dart_eq_of_f_eq {d₁ d₂ : Δ} (hv : D.vtx d₁ = D.vtx d₂)
    (hf : D.f d₁ = D.f d₂) : d₁ = d₂ := by
  have h1 : (⟨d₁, hv⟩ : {d : Δ // D.vtx d = D.vtx d₂})
      = (⟨d₂, rfl⟩ : {d : Δ // D.vtx d = D.vtx d₂}) := by
    apply (D.cubic (D.vtx d₂)).1
    apply Subtype.ext
    exact hf
  exact congrArg Subtype.val h1

/-! ## The partner dart -/

open Classical in
/-- The partner of a support dart: the other support dart at the same
vertex.  Explicit: its flow value is `(s + m_u) + f d`, the third nonzero
point of the vertex plane besides `s + m_u` and `f d`. -/
noncomputable def partnerD (m : V → Γ) (s : Γ) (d : Δ) : Δ :=
  if hd : d ∈ D.Msupp m s then
    ((D.dartEquiv (D.vtx d)).symm
      ⟨s + m (D.vtx d) + D.f d,
       (D.W (D.vtx d)).add_mem
         ((D.mem_Msupp_iff_master m s d).mp hd).1 (D.mem d),
       fun h0 => ((D.mem_Msupp_iff_master m s d).mp hd).2.2
         (char2_add_eq_zero_iff.mp h0)⟩).1
  else d

variable {m : V → Γ} {s : Γ} {d : Δ}

lemma partnerD_vtx (hd : d ∈ D.Msupp m s) :
    D.vtx (D.partnerD m s d) = D.vtx d := by
  unfold partnerD
  rw [dif_pos hd]
  exact ((D.dartEquiv (D.vtx d)).symm _).2

lemma f_partnerD (hd : d ∈ D.Msupp m s) :
    D.f (D.partnerD m s d) = s + m (D.vtx d) + D.f d := by
  unfold partnerD
  rw [dif_pos hd]
  exact D.f_dartEquiv_symm _ _

lemma partnerD_mem (hd : d ∈ D.Msupp m s) :
    D.partnerD m s d ∈ D.Msupp m s := by
  rw [D.mem_Msupp_iff_master, D.partnerD_vtx hd, D.f_partnerD hd]
  obtain ⟨h1, h2, h3⟩ := (D.mem_Msupp_iff_master m s d).mp hd
  refine ⟨h1, h2, fun e => ?_⟩
  exact D.nz d (add_left_cancel (a := s + m (D.vtx d)) (b := (0 : Γ))
    (by rw [add_zero]; exact e)).symm

lemma partnerD_ne (hd : d ∈ D.Msupp m s) : D.partnerD m s d ≠ d := by
  intro e
  have hf := D.f_partnerD hd
  rw [e] at hf
  obtain ⟨-, h2, -⟩ := (D.mem_Msupp_iff_master m s d).mp hd
  apply h2
  exact (add_right_cancel (a := (0 : Γ)) (b := D.f d)
    (c := s + m (D.vtx d)) (by rw [zero_add]; exact hf)).symm

lemma partnerD_partnerD (hd : d ∈ D.Msupp m s) :
    D.partnerD m s (D.partnerD m s d) = d := by
  have hd' := D.partnerD_mem hd
  apply D.dart_eq_of_f_eq
  · rw [D.partnerD_vtx hd', D.partnerD_vtx hd]
  · rw [D.f_partnerD hd', D.partnerD_vtx hd, D.f_partnerD hd]
    exact char2_add_left_eq _ _

/-- Completeness: a support dart at the same vertex is `d` or its partner. -/
lemma eq_or_eq_partnerD (hd : d ∈ D.Msupp m s) {d' : Δ}
    (hv : D.vtx d' = D.vtx d) (hd' : d' ∈ D.Msupp m s) :
    d' = d ∨ d' = D.partnerD m s d := by
  obtain ⟨h1, h2, h3⟩ := (D.mem_Msupp_iff_master m s d).mp hd
  obtain ⟨h1', h2', h3'⟩ := (D.mem_Msupp_iff_master m s d').mp hd'
  rw [hv] at h3'
  -- the three directions of the vertex plane
  have hmem' : D.f d' ∈ D.W (D.vtx d) := by
    have := D.mem d'
    rwa [hv] at this
  rcases (D.plane (D.vtx d)).trichotomy
      ⟨s + m (D.vtx d), h1, h2⟩ ⟨D.f d, D.mem d, D.nz d⟩
      (fun e => h3 e.symm) ⟨D.f d', hmem', D.nz d'⟩ with he | he | he
  · -- `f d' = s + m_u`: contradicts the master condition at `d'`
    exact absurd (congrArg Subtype.val he).symm h3'
  · -- `f d' = f d`
    exact Or.inl (D.dart_eq_of_f_eq hv (congrArg Subtype.val he))
  · -- `f d' = (s + m_u) + f d`
    refine Or.inr (D.dart_eq_of_f_eq
      (hv.trans (D.partnerD_vtx hd).symm) ?_)
    rw [D.f_partnerD hd]
    exact he

/-- **G1** (vertex condition, exactly-two form): a support dart has a unique
companion support dart at its vertex. -/
theorem Msupp_vertex_unique (hd : d ∈ D.Msupp m s) :
    ∃! d', d' ≠ d ∧ D.vtx d' = D.vtx d ∧ d' ∈ D.Msupp m s := by
  refine ⟨D.partnerD m s d,
    ⟨D.partnerD_ne hd, D.partnerD_vtx hd, D.partnerD_mem hd⟩,
    fun d' ⟨hne, hv, hmem⟩ => ?_⟩
  exact (D.eq_or_eq_partnerD hd hv hmem).resolve_left hne

/-! ## The rotation -/

/-- The rotation of a support: step across the edge, then turn at the
vertex.  Its orbits are the cycles. -/
noncomputable def rho (m : V → Γ) (s : Γ) (d : Δ) : Δ :=
  D.partnerD m s (D.σ d)

/-- The inverse rotation. -/
noncomputable def rhoInv (m : V → Γ) (s : Γ) (d : Δ) : Δ :=
  D.σ (D.partnerD m s d)

lemma rho_mem (hm : D.Glued m) (hd : d ∈ D.Msupp m s) :
    D.rho m s d ∈ D.Msupp m s :=
  D.partnerD_mem ((D.Msupp_sigma hm s d).mpr hd)

lemma rho_vtx (hm : D.Glued m) (hd : d ∈ D.Msupp m s) :
    D.vtx (D.rho m s d) = D.vtx (D.σ d) :=
  D.partnerD_vtx ((D.Msupp_sigma hm s d).mpr hd)

lemma rho_ne_sigma (hm : D.Glued m) (hd : d ∈ D.Msupp m s) :
    D.rho m s d ≠ D.σ d :=
  D.partnerD_ne ((D.Msupp_sigma hm s d).mpr hd)

lemma rhoInv_rho (hm : D.Glued m) (hd : d ∈ D.Msupp m s) :
    D.rhoInv m s (D.rho m s d) = d := by
  unfold rho rhoInv
  rw [D.partnerD_partnerD ((D.Msupp_sigma hm s d).mpr hd), D.invol d]

lemma rho_rhoInv (hd : d ∈ D.Msupp m s) :
    D.rho m s (D.rhoInv m s d) = d := by
  unfold rho rhoInv
  rw [D.invol (D.partnerD m s d), D.partnerD_partnerD hd]

/-! ## The cover -/

/-- **G4** (cycle double cover): for a cubic dart structure with a
nowhere-zero flow into a codimension-one plane system, the supports of a
glued gauge form a cycle double cover — σ-closed subgraphs covering every
edge exactly twice, 2-regular wherever present, with the rotation witnessing
the decomposition into cycles as its orbit decomposition. -/
theorem exists_cycle_double_cover
    [Fintype Δ] [DecidableEq Δ] [Fintype V] [DecidableEq V]
    (hcodim : ∀ u : V, Module.finrank (ZMod 2) (Γ ⧸ D.W u) = 1) :
    ∃ M : Γ → Set Δ,
      (∀ s d, D.σ d ∈ M s ↔ d ∈ M s)
      ∧ (∀ d, {s | d ∈ M s}.ncard = 2)
      ∧ (∀ s d, d ∈ M s →
          ∃! d', d' ≠ d ∧ D.vtx d' = D.vtx d ∧ d' ∈ M s)
      ∧ (∀ s, ∃ ρ ρ' : Δ → Δ, ∀ d ∈ M s,
          ρ d ∈ M s ∧ D.vtx (ρ d) = D.vtx (D.σ d) ∧ ρ d ≠ D.σ d
            ∧ ρ' (ρ d) = d ∧ ρ (ρ' d) = d) := by
  obtain ⟨m, hm⟩ := D.exists_glued hcodim
  refine ⟨D.Msupp m, fun s d => D.Msupp_sigma hm s d,
    fun d => D.ncard_setOf_mem_Msupp m d,
    fun s d hd => D.Msupp_vertex_unique hd,
    fun s => ⟨D.rho m s, D.rhoInv m s, fun d hd =>
      ⟨D.rho_mem hm hd, D.rho_vtx hm hd, D.rho_ne_sigma hm hd,
       D.rhoInv_rho hm hd, D.rho_rhoInv hd⟩⟩⟩

end DartFlow

end AffineCDC
