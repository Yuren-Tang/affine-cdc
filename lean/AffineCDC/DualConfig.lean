import AffineCDC.Basic

/-!
# The cross-pairing bit (T5)

The space `dualConfig W` of *legal dual configurations*: families
`η : Dir W → Γ*` with `η_h(h) = 0` and zero sum over the direction triple.
The summation condition is stated over sum-zero triples (`x + y + z = 0`),
which for a plane are exactly the pairwise-distinct triples — no enumeration
of the directions is ever chosen.

* `cross_eq` (**D1**): all six cross-pairings `η_h(h')`, `h ≠ h'`, agree;
* `crossBit`/`crossBitL` (**D2**): the common value `β(η)`, packaged as a
  linear functional on `dualConfig W`;
* `crossBit_eq_zero_iff` (**D3**): `β(η) = 0` iff every `η_h` annihilates
  all of `W`.

Everything holds for an arbitrary `𝔽₂`-vector space `Γ`; `dim Γ = 3` first
enters at T6 (uniqueness of the invariant functional), not here.
-/

namespace AffineCDC

variable {Γ : Type*} [AddCommGroup Γ] [Module (ZMod 2) Γ]
variable {W : Submodule (ZMod 2) Γ}

/-- Legal dual configurations at a plane: `η_h(h) = 0`, and the three
functionals of every sum-zero (equivalently: pairwise distinct) triple of
directions sum to zero. -/
def dualConfig (W : Submodule (ZMod 2) Γ) :
    Submodule (ZMod 2) (Dir W → Module.Dual (ZMod 2) Γ) where
  carrier := {η | (∀ h : Dir W, η h (h : Γ) = 0) ∧
    ∀ x y z : Dir W, (x : Γ) + (y : Γ) + (z : Γ) = 0 →
      η x + η y + η z = 0}
  add_mem' := by
    rintro η η' ⟨h1, h2⟩ ⟨h1', h2'⟩
    refine ⟨fun h => ?_, fun x y z hs => ?_⟩
    · simp [h1 h, h1' h]
    · have key : (η + η') x + (η + η') y + (η + η') z
          = (η x + η y + η z) + (η' x + η' y + η' z) := by
        simp only [Pi.add_apply]
        abel
      rw [key, h2 x y z hs, h2' x y z hs, add_zero]
  zero_mem' := by
    refine ⟨fun h => rfl, fun x y z _ => ?_⟩
    simp
  smul_mem' := by
    rintro c η ⟨h1, h2⟩
    refine ⟨fun h => ?_, fun x y z hs => ?_⟩
    · simp [h1 h]
    · have key : (c • η) x + (c • η) y + (c • η) z
          = c • (η x + η y + η z) := by
        simp only [Pi.smul_apply]
        rw [smul_add, smul_add]
      rw [key, h2 x y z hs, smul_zero]

lemma mem_dualConfig {η : Dir W → Module.Dual (ZMod 2) Γ} :
    η ∈ dualConfig W ↔ (∀ h : Dir W, η h (h : Γ) = 0) ∧
      (∀ x y z : Dir W, (x : Γ) + (y : Γ) + (z : Γ) = 0 →
        η x + η y + η z = 0) :=
  Iff.rfl

/-- Second-argument stability: `η_h` takes one value on the directions
other than `h`. -/
lemma eval_eq_of_ne (hP : IsPlane W) {η : Dir W → Module.Dual (ZMod 2) Γ}
    (hη : η ∈ dualConfig W) {h a b : Dir W} (ha : (a : Γ) ≠ (h : Γ))
    (hb : (b : Γ) ≠ (h : Γ)) : η h (a : Γ) = η h (b : Γ) := by
  by_cases hab : (a : Γ) = (b : Γ)
  · rw [hab]
  · have hba := hP.eq_add_of_ne h a b ha hb hab
    rw [hba, map_add, (mem_dualConfig.mp hη).1 h, add_zero]

/-- Swap symmetry of the cross-pairing. -/
lemma eval_swap (hP : IsPlane W) {η : Dir W → Module.Dual (ZMod 2) Γ}
    (hη : η ∈ dualConfig W) {x y : Dir W} (hyx : (y : Γ) ≠ (x : Γ)) :
    η x (y : Γ) = η y (x : Γ) := by
  set z : Dir W := Dir.add x y hyx with hz
  have hzval : (z : Γ) = (y : Γ) + (x : Γ) := by rw [hz, Dir.add_coe]
  have hzx : (z : Γ) ≠ (x : Γ) := by
    rw [hzval]
    intro e
    exact y.coe_ne_zero (add_right_cancel (a := (y : Γ)) (b := (x : Γ))
      (c := (0 : Γ)) (by rw [zero_add]; exact e))
  have hzy : (z : Γ) ≠ (y : Γ) := by
    rw [hzval]
    intro e
    exact x.coe_ne_zero (add_left_cancel (a := (y : Γ)) (b := (x : Γ))
      (c := (0 : Γ)) (by rw [add_zero]; exact e))
  have hsum : (x : Γ) + (y : Γ) + (z : Γ) = 0 := by
    rw [hzval, add_comm (y : Γ) (x : Γ), char2_add_self]
  have e1 := LinearMap.congr_fun ((mem_dualConfig.mp hη).2 x y z hsum) (z : Γ)
  simp only [LinearMap.add_apply, LinearMap.zero_apply] at e1
  rw [(mem_dualConfig.mp hη).1 z, add_zero,
    eval_eq_of_ne hP hη hzx hyx,
    eval_eq_of_ne hP hη hzy (fun e => hyx e.symm)] at e1
  exact char2_add_eq_zero_iff.mp e1

/-- **D1**: all cross-pairings of a legal configuration agree. -/
theorem cross_eq (hP : IsPlane W) {η : Dir W → Module.Dual (ZMod 2) Γ}
    (hη : η ∈ dualConfig W) {a b c d : Dir W} (hab : (b : Γ) ≠ (a : Γ))
    (hcd : (d : Γ) ≠ (c : Γ)) : η a (b : Γ) = η c (d : Γ) := by
  by_cases hca : (c : Γ) = (a : Γ)
  · have hc : c = a := Subtype.ext hca
    rw [hc]
    exact eval_eq_of_ne hP hη hab (by rw [← hca]; exact hcd)
  · by_cases hda : (d : Γ) = (a : Γ)
    · have h1 : η a (b : Γ) = η a (c : Γ) :=
        eval_eq_of_ne hP hη hab (fun e => hca e)
      have h2 : η a (c : Γ) = η c (a : Γ) := eval_swap hP hη (fun e => hca e)
      have h3 : η c (a : Γ) = η c (d : Γ) := by rw [hda]
      rw [h1, h2, h3]
    · have h1 : η a (b : Γ) = η a (c : Γ) :=
        eval_eq_of_ne hP hη hab (fun e => hca e)
      have h2 : η a (c : Γ) = η c (a : Γ) := eval_swap hP hη (fun e => hca e)
      have h3 : η c (a : Γ) = η c (d : Γ) :=
        eval_eq_of_ne hP hη (fun e => hca e.symm) hcd
      rw [h1, h2, h3]

/-- **D2**: the cross-pairing bit `β(η)`. -/
noncomputable def crossBit (hP : IsPlane W) (η : dualConfig W) : ZMod 2 :=
  η.1 hP.dir₀ ((hP.other hP.dir₀ : Γ))

lemma crossBit_def (hP : IsPlane W) (η : dualConfig W) :
    crossBit hP η = η.1 hP.dir₀ ((hP.other hP.dir₀ : Γ)) := rfl

/-- Every cross-pairing computes `β`. -/
theorem crossBit_eq (hP : IsPlane W) (η : dualConfig W) {h h' : Dir W}
    (hne : (h' : Γ) ≠ (h : Γ)) : η.1 h (h' : Γ) = crossBit hP η :=
  cross_eq hP η.2 hne (hP.other_ne hP.dir₀)

/-- **D2**, packaged: `β` is a linear functional on `dualConfig W`. -/
noncomputable def crossBitL (hP : IsPlane W) :
    (dualConfig W) →ₗ[ZMod 2] ZMod 2 where
  toFun := crossBit hP
  map_add' η η' := rfl
  map_smul' c η := rfl

/-- **D3**: `β(η) = 0` iff every `η_h` annihilates `W`. -/
theorem crossBit_eq_zero_iff (hP : IsPlane W) (η : dualConfig W) :
    crossBit hP η = 0 ↔ ∀ h : Dir W, ∀ w ∈ W, η.1 h w = 0 := by
  constructor
  · intro hβ h w hw
    by_cases hw0 : w = 0
    · rw [hw0, map_zero]
    · by_cases hwh : w = (h : Γ)
      · rw [hwh]
        exact (mem_dualConfig.mp η.2).1 h
      · exact (crossBit_eq hP η (h' := ⟨w, hw, hw0⟩) hwh).trans hβ
  · intro hall
    rw [crossBit_def]
    exact hall hP.dir₀ _ (hP.other hP.dir₀).coe_mem

end AffineCDC
