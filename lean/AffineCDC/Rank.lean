import AffineCDC.Basic

/-!
# The rank bridge: `finrank = 2` gives a plane

`IsPlane` (the intrinsic Klein-triple structure used throughout the
development) is implied by the standard hypothesis `finrank 𝔽₂ W = 2`.

The proof transfers along a linear equivalence `W ≃ₗ 𝔽₂²` and settles the
three finite statements in the concrete model by `decide` — coordinates are
quarantined in this one file and never touch the main development.
-/

namespace AffineCDC

variable {Γ : Type*} [AddCommGroup Γ] [Module (ZMod 2) Γ]

/-- The concrete model: `𝔽₂²`. -/
private abbrev V2 : Type := Fin 2 → ZMod 2

private lemma model_nonempty : ∃ u : V2, u ≠ 0 := by decide

private lemma model_exists_ne : ∀ u : V2, u ≠ 0 → ∃ v : V2, v ≠ 0 ∧ v ≠ u := by
  decide

private lemma model_eq_add : ∀ h a b : V2,
    (h ≠ 0 ∧ a ≠ 0 ∧ b ≠ 0 ∧ a ≠ h ∧ b ≠ h ∧ a ≠ b) → b = a + h := by decide

/-- A two-dimensional subspace over `𝔽₂` is a plane in the intrinsic sense. -/
theorem IsPlane.of_finrank_eq_two (W : Submodule (ZMod 2) Γ)
    (hr : Module.finrank (ZMod 2) W = 2) : IsPlane W := by
  haveI : Module.Finite (ZMod 2) W :=
    Module.finite_of_finrank_pos (by rw [hr]; norm_num)
  have hr2 : Module.finrank (ZMod 2) V2 = 2 := by simp
  let e : W ≃ₗ[ZMod 2] V2 := LinearEquiv.ofFinrankEq _ _ (hr.trans hr2.symm)
  have hsymm0 : ∀ v : V2, v ≠ 0 → e.symm v ≠ 0 := by
    intro v hv h0
    apply hv
    rw [← e.apply_symm_apply v, h0, map_zero]
  have hfwd0 : ∀ (u : Dir W) (uW : W), (uW : Γ) = (u : Γ) → e uW ≠ 0 := by
    intro u uW huW e0
    apply u.coe_ne_zero
    rw [← huW]
    exact congrArg Subtype.val (e.map_eq_zero_iff.mp e0)
  constructor
  · -- nonempty
    obtain ⟨u, hu⟩ := model_nonempty
    exact ⟨(e.symm u : Γ), (e.symm u).2,
      fun h0 => hsymm0 u hu (Subtype.ext h0)⟩
  · -- exists_ne
    intro h
    obtain ⟨v, hv0, hvu⟩ :=
      model_exists_ne (e ⟨(h : Γ), h.coe_mem⟩) (hfwd0 h _ rfl)
    refine ⟨⟨(e.symm v : Γ), (e.symm v).2,
      fun h0 => hsymm0 v hv0 (Subtype.ext h0)⟩, ?_⟩
    intro hval
    apply hvu
    have h2 : e.symm v = (⟨(h : Γ), h.coe_mem⟩ : W) := Subtype.ext hval
    rw [← e.apply_symm_apply v, h2]
  · -- eq_add_of_ne
    intro h a b hah hbh hab
    have hinj : ∀ u w : W, e u = e w → (u : Γ) = (w : Γ) :=
      fun u w e0 => congrArg Subtype.val (e.injective e0)
    have key := model_eq_add
      (e ⟨(h : Γ), h.coe_mem⟩) (e ⟨(a : Γ), a.coe_mem⟩) (e ⟨(b : Γ), b.coe_mem⟩)
      ⟨hfwd0 h _ rfl, hfwd0 a _ rfl, hfwd0 b _ rfl,
       fun e0 => hah (hinj _ _ e0), fun e0 => hbh (hinj _ _ e0),
       fun e0 => hab (hinj _ _ e0)⟩
    have hW : (⟨(b : Γ), b.coe_mem⟩ : W)
        = (⟨(a : Γ), a.coe_mem⟩ : W) + (⟨(h : Γ), h.coe_mem⟩ : W) := by
      apply e.injective
      rw [map_add]
      exact key
    exact congrArg Subtype.val hW

/-- Converse bridge: a plane has `finrank = 2`.  With
`IsPlane.of_finrank_eq_two` this shows the intrinsic Klein-triple structure
is *equivalent* to the standard dimension hypothesis. -/
theorem IsPlane.finrank_eq_two {W : Submodule (ZMod 2) Γ} (hP : IsPlane W) :
    Module.finrank (ZMod 2) W = 2 := by
  set x : Dir W := hP.dir₀ with hxdef
  set y : Dir W := hP.other x with hydef
  have hyx : (y : Γ) ≠ (x : Γ) := hP.other_ne x
  set xW : W := ⟨(x : Γ), x.coe_mem⟩ with hxW
  set yW : W := ⟨(y : Γ), y.coe_mem⟩ with hyW
  have hli : LinearIndependent (ZMod 2) ![xW, yW] := by
    rw [linearIndependent_fin2]
    simp only [Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_zero]
    constructor
    · intro e
      have e' := Subtype.ext_iff.mp e
      exact y.coe_ne_zero e'
    · intro c
      have h01 : c = 0 ∨ c = 1 := by revert c; decide
      rcases h01 with rfl | rfl
      · rw [zero_smul]
        intro e
        have e' := Subtype.ext_iff.mp e
        exact x.coe_ne_zero e'.symm
      · rw [one_smul]
        intro e
        have e' := Subtype.ext_iff.mp e
        exact hyx e'
  have hspan : ⊤ ≤ Submodule.span (ZMod 2) (Set.range ![xW, yW]) := by
    intro w _
    have hx_mem : xW ∈ Set.range ![xW, yW] := ⟨0, rfl⟩
    have hy_mem : yW ∈ Set.range ![xW, yW] := ⟨1, rfl⟩
    by_cases hw0 : (w : Γ) = 0
    · have : w = 0 := Subtype.ext hw0
      rw [this]
      exact Submodule.zero_mem _
    · set d : Dir W := ⟨(w : Γ), w.2, hw0⟩ with hd
      rcases hP.trichotomy x y hyx d with h1 | h1 | h1
      · have hval := Subtype.ext_iff.mp h1
        have hw : w = xW := by
          apply Subtype.ext
          exact hval
        rw [hw]
        exact Submodule.subset_span hx_mem
      · have hval := Subtype.ext_iff.mp h1
        have hw : w = yW := by
          apply Subtype.ext
          exact hval
        rw [hw]
        exact Submodule.subset_span hy_mem
      · have hw : w = xW + yW := by
          apply Subtype.ext
          exact h1
        rw [hw]
        exact Submodule.add_mem _ (Submodule.subset_span hx_mem)
          (Submodule.subset_span hy_mem)
  have hb := Module.Basis.mk hli hspan
  rw [Module.finrank_eq_card_basis hb]
  simp

end AffineCDC
