import AffineCDC.DualConfig
import AffineCDC.LocalClassification
import Mathlib.LinearAlgebra.Projection
import Mathlib.GroupTheory.GroupAction.Ring

/-!
# Uniqueness of the invariant functional (T6)

The cross-pairing bit `β` is the *only* nonzero linear functional on
`dualConfig W` invariant under shears — for an **arbitrary** `𝔽₂`-vector
space `Γ` (**E3**, v2 form).

A *shear* is taken in action-ready form: a linear `s : Γ →ₗ Γ` with values
in `W` and vanishing on `W`; the corresponding automorphism is `1 + s` (an
involution in characteristic two), and its action on a configuration is
`η_h ↦ η_h + η_h ∘ s` (`shearConfig`; directions are fixed since shears fix
`W` pointwise).

* `baseConfig hP` — an explicit configuration with `β = 1`, built from a
  complement projection (`projW`) and separating functionals (`sepFun`);
  all choices are quarantined here and never appear in statements;
* `ShearInvariant.eq_zero_of_crossBit_eq_zero` — the crux: a shear-invariant
  functional kills `ker β`;
* `ShearInvariant.eq_smul_crossBitL` / `eq_zero_or_eq_crossBitL` (**E3**):
  a shear-invariant functional is a scalar multiple of `β`.
-/

namespace AffineCDC

variable {Γ : Type*} [AddCommGroup Γ] [Module (ZMod 2) Γ]
variable {W : Submodule (ZMod 2) Γ}

/-! ## Shears and their action on configurations -/

/-- The action of the shear `1 + s` on a family of functionals:
precomposition, `η_h ↦ η_h + η_h ∘ s`. -/
def shearConfig (s : Γ →ₗ[ZMod 2] Γ) (η : Dir W → Module.Dual (ZMod 2) Γ) :
    Dir W → Module.Dual (ZMod 2) Γ :=
  fun h => η h + (η h).comp s

lemma shearConfig_mem (s : Γ →ₗ[ZMod 2] Γ) (hsK : ∀ w ∈ W, s w = 0)
    {η : Dir W → Module.Dual (ZMod 2) Γ} (hη : η ∈ dualConfig W) :
    shearConfig s η ∈ dualConfig W := by
  refine ⟨fun h => ?_, fun x y z hs => ?_⟩
  · show η h (h : Γ) + η h (s (h : Γ)) = 0
    rw [hsK (h : Γ) h.coe_mem, map_zero, add_zero]
    exact (mem_dualConfig.mp hη).1 h
  · show (η x + (η x).comp s) + (η y + (η y).comp s) + (η z + (η z).comp s) = 0
    have key : (η x + (η x).comp s) + (η y + (η y).comp s)
          + (η z + (η z).comp s)
        = (η x + η y + η z) + (η x + η y + η z).comp s := by
      rw [LinearMap.add_comp, LinearMap.add_comp]
      abel
    rw [key, (mem_dualConfig.mp hη).2 x y z hs, LinearMap.zero_comp, add_zero]

/-- Invariance of a functional on `dualConfig W` under all shears. -/
def ShearInvariant (ℓ : dualConfig W →ₗ[ZMod 2] ZMod 2) : Prop :=
  ∀ (s : Γ →ₗ[ZMod 2] Γ) (_ : ∀ γ, s γ ∈ W) (hsK : ∀ w ∈ W, s w = 0)
    (η : dualConfig W),
    ℓ ⟨shearConfig s η.1, shearConfig_mem s hsK η.2⟩ = ℓ η

/-! ## An explicit configuration with `β = 1` -/

section BaseConfig

variable (hP : IsPlane W)

private lemma exists_sepFun (h : Dir W) :
    ∃ φ : Module.Dual (ZMod 2) (LineSpace h), φ (hP.kappa h) = 1 := by
  have hne : ¬ ∀ φ : Module.Dual (ZMod 2) (LineSpace h),
      φ (hP.kappa h) = 0 := by
    rw [Module.forall_dual_apply_eq_zero_iff]
    exact hP.kappa_ne_zero h
  obtain ⟨φ, hφ⟩ := not_forall.mp hne
  have h01 : ∀ c : ZMod 2, c ≠ 0 → c = 1 := by decide
  exact ⟨φ, h01 _ hφ⟩

/-- A functional on the line space separating `κ_h` from `0`
(choice, quarantined). -/
noncomputable def sepFun (h : Dir W) :
    Module.Dual (ZMod 2) (LineSpace h) :=
  (exists_sepFun hP h).choose

lemma sepFun_kappa (h : Dir W) : sepFun hP h (hP.kappa h) = 1 :=
  (exists_sepFun hP h).choose_spec

/-- A chosen projection `Γ →ₗ W` restricting to the identity on `W`
(complement choice, quarantined). -/
noncomputable def projW (W : Submodule (ZMod 2) Γ) : Γ →ₗ[ZMod 2] W :=
  Submodule.projectionOnto W W.exists_isCompl.choose
    W.exists_isCompl.choose_spec

lemma projW_coe (w : W) : projW W (w : Γ) = w :=
  Submodule.projectionOnto_apply_left W.exists_isCompl.choose_spec w

/-- Values of the separating functional along the plane. -/
lemma sepLine_self (h : Dir W) : sepFun hP h (lineMk h (h : Γ)) = 0 := by
  rw [lineMk_self, map_zero]

lemma sepLine_ne (h a : Dir W) (ha : (a : Γ) ≠ (h : Γ)) :
    sepFun hP h (lineMk h (a : Γ)) = 1 := by
  rw [← hP.kappa_eq h a ha, sepFun_kappa]

/-- The `h`-component of the base configuration:
`γ ↦ sepFun h (lineMk h (projW γ))`. -/
noncomputable def baseFun (h : Dir W) : Module.Dual (ZMod 2) Γ :=
  (sepFun hP h).comp ((lineMk h).comp (W.subtype.comp (projW W)))

lemma baseFun_apply (h : Dir W) (γ : Γ) :
    baseFun hP h γ = sepFun hP h (lineMk h ((projW W γ : W) : Γ)) := rfl

lemma baseFun_coe (h : Dir W) (w : W) :
    baseFun hP h (w : Γ) = sepFun hP h (lineMk h (w : Γ)) := by
  rw [baseFun_apply, projW_coe]

lemma baseFun_self (h : Dir W) : baseFun hP h (h : Γ) = 0 := by
  rw [baseFun_coe hP h ⟨(h : Γ), h.coe_mem⟩, sepLine_self]

lemma baseFun_ne (h a : Dir W) (ha : (a : Γ) ≠ (h : Γ)) :
    baseFun hP h (a : Γ) = 1 := by
  rw [baseFun_coe hP h ⟨(a : Γ), a.coe_mem⟩, sepLine_ne hP h a ha]

/-- The base configuration is legal. -/
lemma baseFun_mem : (fun h => baseFun hP h) ∈ dualConfig W := by
  refine ⟨baseFun_self hP, fun x y z hs => ?_⟩
  -- pairwise distinctness from the sum-zero triple
  have hyx : (y : Γ) ≠ (x : Γ) := by
    intro e
    apply z.coe_ne_zero
    rw [e, char2_add_self, zero_add] at hs
    exact hs
  have hzx : (z : Γ) ≠ (x : Γ) := by
    intro e
    apply y.coe_ne_zero
    rw [e, add_comm (x : Γ) (y : Γ), add_assoc, char2_add_self, add_zero] at hs
    exact hs
  have hzy : (z : Γ) ≠ (y : Γ) := by
    intro e
    apply x.coe_ne_zero
    rw [e, add_assoc, char2_add_self, add_zero] at hs
    exact hs
  ext γ
  show baseFun hP x γ + baseFun hP y γ + baseFun hP z γ = 0
  rw [baseFun_apply, baseFun_apply, baseFun_apply]
  set w : W := projW W γ with hw
  by_cases hw0 : (w : Γ) = 0
  · rw [hw0]
    show sepFun hP x (lineMk x 0) + sepFun hP y (lineMk y 0)
        + sepFun hP z (lineMk z 0) = 0
    rw [map_zero, map_zero, map_zero, map_zero, map_zero, map_zero,
      add_zero, add_zero]
  · set d : Dir W := ⟨(w : Γ), w.2, hw0⟩ with hd
    have hwd : (w : Γ) = (d : Γ) := rfl
    rw [hwd]
    rcases hP.trichotomy x y hyx d with h1 | h1 | h1
    · rw [h1]
      rw [show sepFun hP x (lineMk x (x : Γ)) = 0 from sepLine_self hP x,
        sepLine_ne hP y x (fun e => hyx e.symm),
        sepLine_ne hP z x (Ne.symm hzx)]
      decide
    · rw [h1]
      rw [sepLine_ne hP x y hyx,
        show sepFun hP y (lineMk y (y : Γ)) = 0 from sepLine_self hP y,
        sepLine_ne hP z y (Ne.symm hzy)]
      decide
    · have hdz : (d : Γ) = (z : Γ) := by
        rw [h1]
        exact char2_add_eq_zero_iff.mp hs
      have hdx : (d : Γ) ≠ (x : Γ) := by
        rw [h1]
        intro e
        exact y.coe_ne_zero (add_left_cancel (a := (x : Γ)) (b := (y : Γ))
          (c := (0 : Γ)) (by rw [add_zero]; exact e))
      have hdy : (d : Γ) ≠ (y : Γ) := by
        rw [h1]
        intro e
        exact x.coe_ne_zero (add_right_cancel (a := (x : Γ)) (b := (y : Γ))
          (c := (0 : Γ)) (by rw [zero_add]; exact e))
      rw [sepLine_ne hP x d hdx, sepLine_ne hP y d hdy, hdz,
        show sepFun hP z (lineMk z (z : Γ)) = 0 from sepLine_self hP z]
      decide

/-- The base configuration, bundled: an explicit element of `dualConfig W`
with `β = 1`. -/
noncomputable def baseConfig : dualConfig W :=
  ⟨fun h => baseFun hP h, baseFun_mem hP⟩

lemma crossBit_baseConfig : crossBit hP (baseConfig hP) = 1 := by
  rw [crossBit_def]
  exact baseFun_ne hP hP.dir₀ (hP.other hP.dir₀) (hP.other_ne hP.dir₀)

end BaseConfig

/-! ## The uniqueness theorem -/

/-- Crux: a shear-invariant functional vanishes on `ker β`. -/
theorem ShearInvariant.eq_zero_of_crossBit_eq_zero (hP : IsPlane W)
    {ℓ : dualConfig W →ₗ[ZMod 2] ZMod 2} (hℓ : ShearInvariant ℓ)
    {η : dualConfig W} (hβ : crossBit hP η = 0) : ℓ η = 0 := by
  set x : Dir W := hP.dir₀ with hx
  set y : Dir W := hP.other x with hy
  have hyx : (y : Γ) ≠ (x : Γ) := hP.other_ne x
  have hkill : ∀ h : Dir W, ∀ w ∈ W, η.1 h w = 0 :=
    (crossBit_eq_zero_iff hP η).mp hβ
  -- the shear associated with `η`
  set s : Γ →ₗ[ZMod 2] Γ :=
    (η.1 x).smulRight (y : Γ) + (η.1 y).smulRight (x : Γ) with hs
  have hsval : ∀ γ, s γ = η.1 x γ • (y : Γ) + η.1 y γ • (x : Γ) := by
    intro γ
    rw [hs]
    simp [LinearMap.smulRight_apply]
  have hsW : ∀ γ, s γ ∈ W := by
    intro γ
    rw [hsval]
    exact W.add_mem (W.smul_mem _ y.coe_mem) (W.smul_mem _ x.coe_mem)
  have hsK : ∀ w ∈ W, s w = 0 := by
    intro w hw
    rw [hsval, hkill x w hw, hkill y w hw, zero_smul, zero_smul, add_zero]
  -- shearing the base configuration adds `η`
  have hkey : (⟨shearConfig s (baseConfig hP).1,
      shearConfig_mem s hsK (baseConfig hP).2⟩ : dualConfig W)
      = baseConfig hP + η := by
    apply Subtype.ext
    funext h
    show baseFun hP h + (baseFun hP h).comp s = baseFun hP h + η.1 h
    congr 1
    ext γ
    show baseFun hP h (s γ) = η.1 h γ
    rw [hsval, map_add, map_smul, map_smul]
    rcases hP.trichotomy x y hyx h with h1 | h1 | h1
    · rw [h1, baseFun_ne hP x y hyx, baseFun_self hP x, smul_eq_mul,
        smul_eq_mul, mul_one, mul_zero, add_zero]
    · rw [h1, baseFun_self hP y, baseFun_ne hP y x (fun e => hyx e.symm),
        smul_eq_mul, smul_eq_mul, mul_zero, mul_one, zero_add]
    · have hyh : (y : Γ) ≠ (h : Γ) := by
        rw [h1]
        intro e
        exact x.coe_ne_zero (add_right_cancel (a := (0 : Γ)) (b := (y : Γ))
          (c := (x : Γ)) (by rw [zero_add]; exact e)).symm
      have hxh : (x : Γ) ≠ (h : Γ) := by
        rw [h1]
        intro e
        exact y.coe_ne_zero (add_left_cancel (a := (x : Γ)) (b := (0 : Γ))
          (c := (y : Γ)) (by rw [add_zero]; exact e)).symm
      rw [baseFun_ne hP h y hyh, baseFun_ne hP h x hxh, smul_eq_mul,
        smul_eq_mul, mul_one, mul_one]
      have hsum : (x : Γ) + (y : Γ) + (h : Γ) = 0 := by
        rw [h1, char2_add_self]
      have e1 := LinearMap.congr_fun
        ((mem_dualConfig.mp η.2).2 x y h hsum) γ
      simp only [LinearMap.add_apply, LinearMap.zero_apply] at e1
      exact char2_add_eq_zero_iff.mp e1
  have hinv := hℓ s hsW hsK (baseConfig hP)
  rw [hkey, map_add] at hinv
  exact add_left_cancel (a := ℓ (baseConfig hP)) (b := ℓ η) (c := (0 : ZMod 2))
    (by rw [add_zero]; exact hinv)

/-- **E3** (uniqueness, arbitrary `Γ`): a shear-invariant functional on the
configuration space is a scalar multiple of the cross-pairing bit. -/
theorem ShearInvariant.eq_smul_crossBitL (hP : IsPlane W)
    {ℓ : dualConfig W →ₗ[ZMod 2] ZMod 2} (hℓ : ShearInvariant ℓ) :
    ℓ = ℓ (baseConfig hP) • crossBitL hP := by
  ext η
  rw [LinearMap.smul_apply, smul_eq_mul]
  have h01 : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
  rcases h01 (crossBit hP η) with h0 | h1
  · rw [show crossBitL hP η = crossBit hP η from rfl, h0, mul_zero]
    exact hℓ.eq_zero_of_crossBit_eq_zero hP h0
  · have hβ0 : crossBit hP (η + baseConfig hP) = 0 := by
      rw [show crossBit hP (η + baseConfig hP)
          = crossBit hP η + crossBit hP (baseConfig hP)
          from map_add (crossBitL hP) _ _, h1, crossBit_baseConfig hP]
      decide
    have hz := hℓ.eq_zero_of_crossBit_eq_zero hP hβ0
    rw [map_add] at hz
    rw [show crossBitL hP η = crossBit hP η from rfl, h1, mul_one]
    exact char2_add_eq_zero_iff.mp hz

/-- **E3**, disjunctive form: the only shear-invariant functionals are `0`
and `β`. -/
theorem ShearInvariant.eq_zero_or_eq_crossBitL (hP : IsPlane W)
    {ℓ : dualConfig W →ₗ[ZMod 2] ZMod 2} (hℓ : ShearInvariant ℓ) :
    ℓ = 0 ∨ ℓ = crossBitL hP := by
  have h01 : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
  rcases h01 (ℓ (baseConfig hP)) with h | h
  · left
    rw [hℓ.eq_smul_crossBitL hP, h, zero_smul]
  · right
    rw [hℓ.eq_smul_crossBitL hP, h, one_smul]

end AffineCDC
