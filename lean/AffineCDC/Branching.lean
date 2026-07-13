import AffineCDC.DualConfig

/-!
# The branching identity (T7, F1 — graph-free core)

For a plane `W` of **codimension one** (`finrank (Γ ⧸ W) = 1`, i.e.
`dim Γ = 3`), the cross-pairing bit of a legal configuration is computed by
the support count:

`β(η) = #{h : η_h ≠ 0} (mod 2)`  (`crossBit_eq_parity`, stated over any
sum-zero triple of directions).

This is the **only** point of the whole development where the dimension of
`Γ` enters; the codimension-one hypothesis is used exactly once, through
`annihilator_unique` (the annihilator of `W` contains a unique nonzero
functional).  For `codim W ≥ 2` the identity fails (see the paper spec
T7 F1(2)); the global cancellation (F2) consumes precisely this identity.
-/

namespace AffineCDC

open Module

variable {Γ : Type*} [AddCommGroup Γ] [Module (ZMod 2) Γ]
variable {W : Submodule (ZMod 2) Γ}

/-- The nonvanishing bit of a functional. -/
noncomputable def nzBit (φ : Module.Dual (ZMod 2) Γ) : ZMod 2 :=
  haveI := Classical.dec (φ = 0)
  if φ = 0 then 0 else 1

@[simp] lemma nzBit_zero : nzBit (0 : Module.Dual (ZMod 2) Γ) = 0 := by
  simp [nzBit]

lemma nzBit_of_eq_zero {φ : Module.Dual (ZMod 2) Γ} (h : φ = 0) :
    nzBit φ = 0 := by
  simp [nzBit, h]

lemma nzBit_of_ne_zero {φ : Module.Dual (ZMod 2) Γ} (h : φ ≠ 0) :
    nzBit φ = 1 := by
  simp [nzBit, h]

/-- In codimension one, the annihilator of `W` has a unique nonzero
element. -/
lemma annihilator_unique (hcodim : finrank (ZMod 2) (Γ ⧸ W) = 1)
    {φ φ' : Module.Dual (ZMod 2) Γ}
    (hφW : ∀ w ∈ W, φ w = 0) (hφ'W : ∀ w ∈ W, φ' w = 0)
    (hφ : φ ≠ 0) (hφ' : φ' ≠ 0) : φ = φ' := by
  haveI : Module.Finite (ZMod 2) (Γ ⧸ W) :=
    Module.finite_of_finrank_pos (by omega)
  -- a generator of the quotient line
  have hnt : Nontrivial (Γ ⧸ W) := by
    by_contra hns
    rw [not_nontrivial_iff_subsingleton] at hns
    rw [Module.finrank_zero_iff.mpr hns] at hcodim
    omega
  obtain ⟨q₀, hq₀⟩ := exists_ne (0 : Γ ⧸ W)
  obtain ⟨γ₀, rfl⟩ := Submodule.Quotient.mk_surjective W q₀
  have hgen := (finrank_eq_one_iff_of_nonzero' _ hq₀).mp hcodim
  -- a `W`-killing functional is determined by its value at `γ₀`
  have hval : ∀ (ψ : Module.Dual (ZMod 2) Γ), (∀ w ∈ W, ψ w = 0) →
      ∀ (γ : Γ) (c : ZMod 2),
        c • (Submodule.Quotient.mk γ₀ : Γ ⧸ W) = Submodule.Quotient.mk γ →
        ψ γ = c * ψ γ₀ := by
    intro ψ hψ γ c hc
    have hmem : γ + c • γ₀ ∈ W := by
      have : (Submodule.Quotient.mk γ : Γ ⧸ W)
          = Submodule.Quotient.mk (c • γ₀) := by
        rw [Submodule.Quotient.mk_smul, ← hc]
      rw [Submodule.Quotient.eq, char2_sub] at this
      exact this
    have h0 := hψ _ hmem
    rw [map_add, map_smul] at h0
    have := char2_add_eq_zero_iff.mp h0
    rwa [smul_eq_mul] at this
  -- nonzero `W`-killing functionals take value `1` at `γ₀`
  have hone : ∀ (ψ : Module.Dual (ZMod 2) Γ), (∀ w ∈ W, ψ w = 0) →
      ψ ≠ 0 → ψ γ₀ = 1 := by
    intro ψ hψ hψ0
    have h01 : ∀ c : ZMod 2, c ≠ 0 → c = 1 := by decide
    apply h01
    intro h0
    apply hψ0
    ext γ
    obtain ⟨c, hc⟩ := hgen (Submodule.Quotient.mk γ)
    rw [hval ψ hψ γ c hc, h0, mul_zero]
    simp
  ext γ
  obtain ⟨c, hc⟩ := hgen (Submodule.Quotient.mk γ)
  rw [hval φ hφW γ c hc, hval φ' hφ'W γ c hc, hone φ hφW hφ, hone φ' hφ'W hφ']

/-- **F1** (branching identity): in codimension one, the cross-pairing bit
is the parity of the support of the configuration, over any sum-zero triple
of directions. -/
theorem crossBit_eq_parity (hP : IsPlane W)
    (hcodim : finrank (ZMod 2) (Γ ⧸ W) = 1) (η : dualConfig W)
    {x y z : Dir W} (hs : (x : Γ) + (y : Γ) + (z : Γ) = 0) :
    crossBit hP η = nzBit (η.1 x) + nzBit (η.1 y) + nzBit (η.1 z) := by
  have hsum := (mem_dualConfig.mp η.2).2 x y z hs
  have h01 : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
  rcases h01 (crossBit hP η) with hβ | hβ
  · -- `β = 0`: all components annihilate `W`; nonzero ones coincide
    have hkill := (crossBit_eq_zero_iff hP η).mp hβ
    rw [hβ]
    by_cases hx0 : η.1 x = 0 <;> by_cases hy0 : η.1 y = 0 <;>
      by_cases hz0 : η.1 z = 0
    · rw [nzBit_of_eq_zero hx0, nzBit_of_eq_zero hy0, nzBit_of_eq_zero hz0]
      decide
    · -- (0,0,≠): contradicts the sum
      exfalso
      rw [hx0, hy0, zero_add, zero_add] at hsum
      exact hz0 hsum
    · exfalso
      rw [hx0, hz0, zero_add, add_zero] at hsum
      exact hy0 hsum
    · rw [nzBit_of_eq_zero hx0, nzBit_of_ne_zero hy0, nzBit_of_ne_zero hz0]
      decide
    · exfalso
      rw [hy0, hz0, add_zero, add_zero] at hsum
      exact hx0 hsum
    · rw [nzBit_of_ne_zero hx0, nzBit_of_eq_zero hy0, nzBit_of_ne_zero hz0]
      decide
    · rw [nzBit_of_ne_zero hx0, nzBit_of_ne_zero hy0, nzBit_of_eq_zero hz0]
      decide
    · -- (≠,≠,≠): impossible when `β = 0`
      exfalso
      have e1 : η.1 x = η.1 y :=
        annihilator_unique hcodim (hkill x) (hkill y) hx0 hy0
      have e2 : η.1 x = η.1 z :=
        annihilator_unique hcodim (hkill x) (hkill z) hx0 hz0
      rw [← e1, ← e2, char2_add_self, zero_add] at hsum
      exact hx0 hsum
  · -- `β = 1`: all components are nonzero
    have hall : ∀ h : Dir W, η.1 h ≠ 0 := by
      intro h h0
      have hc := crossBit_eq hP η (h' := hP.other h) (hP.other_ne h)
      rw [h0, hβ] at hc
      simp at hc
    rw [hβ, nzBit_of_ne_zero (hall x), nzBit_of_ne_zero (hall y),
      nzBit_of_ne_zero (hall z)]
    decide

end AffineCDC
