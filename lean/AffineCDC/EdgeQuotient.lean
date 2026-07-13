import AffineCDC.LocalClassification
import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Edge quotients (T3)

The universal property of the line space and the uniqueness of `κ`:

* **B1** (two-point sets = cosets) is `coset_eq_pair` in `OppositeFiber.lean`;
* **B2** (`lineLift`, `lineLift_lineMk`, `lineLift_unique`): any linear map
  killing the direction `h` factors uniquely through `LineSpace h` — the
  precise sense in which `Q_e` is *forced* once the two base points of a line
  are identified.  The `ϵ_e` of the original manuscript is the lifting
  variable of this quotient equation;
* **B3** (`kappa_mem_map`, `eq_kappa_of_ne_zero`, `map_eq_pair`): the image
  of `W` in `LineSpace h` is `{0, κ_h}`, so `κ_h` is its unique nonzero
  element.  This is the primal form of the manuscript's "unique nonzero dual
  vector vanishing on `W`" — no duality, no `dim Γ = 3`;
* **B4** (`localFamily_apply`, `existsUnique_label`): the `h`-line of
  `Φ_W(m)` has quotient parameter `[m] + κ_h`, and every even family admits a
  unique deleted point realizing its labels in this affine form.
-/

namespace AffineCDC

variable {Γ : Type*} [AddCommGroup Γ] [Module (ZMod 2) Γ]
variable {W : Submodule (ZMod 2) Γ}

/-! ## B2: the universal property -/

section UniversalProperty

variable {T : Type*} [AddCommGroup T] [Module (ZMod 2) T]

/-- Any linear map killing the direction factors through the line space. -/
def lineLift (h : Dir W) (q : Γ →ₗ[ZMod 2] T) (hq : q (h : Γ) = 0) :
    LineSpace h →ₗ[ZMod 2] T :=
  Submodule.liftQSpanSingleton (h : Γ) q hq

@[simp] lemma lineLift_lineMk (h : Dir W) (q : Γ →ₗ[ZMod 2] T)
    (hq : q (h : Γ) = 0) (s : Γ) :
    lineLift h q hq (lineMk h s) = q s :=
  Submodule.liftQSpanSingleton_apply (h : Γ) q hq s

/-- The factorization is unique: `LineSpace h` is initial among targets of
linear maps killing `h`. -/
lemma lineLift_unique (h : Dir W) (q : Γ →ₗ[ZMod 2] T) (hq : q (h : Γ) = 0)
    (φ : LineSpace h →ₗ[ZMod 2] T) (hφ : ∀ s, φ (lineMk h s) = q s) :
    φ = lineLift h q hq := by
  apply Submodule.linearMap_qext
  ext s
  show φ (lineMk h s) = lineLift h q hq (lineMk h s)
  rw [hφ s, lineLift_lineMk]

end UniversalProperty

/-! ## B3: `κ` is the unique nonzero element of the image of `W` -/

lemma kappa_mem_map (hP : IsPlane W) (h : Dir W) :
    hP.kappa h ∈ W.map (lineMk h) :=
  Submodule.mem_map.mpr ⟨(hP.other h : Γ), (hP.other h).coe_mem, rfl⟩

/-- Any nonzero element of the image of `W` in the line space is `κ`. -/
theorem eq_kappa_of_ne_zero (hP : IsPlane W) (h : Dir W) {x : LineSpace h}
    (hx : x ∈ W.map (lineMk h)) (hx0 : x ≠ 0) : x = hP.kappa h := by
  obtain ⟨w, hw, rfl⟩ := Submodule.mem_map.mp hx
  have hw0 : w ≠ 0 := fun e => hx0 (by rw [e, map_zero])
  have hwh : w ≠ (h : Γ) := fun e => hx0 (by rw [e, lineMk_self])
  exact (hP.kappa_eq h ⟨w, hw, hw0⟩ hwh).symm

/-- The image of `W` in the line space is exactly the pair `{0, κ_h}`:
it is one-dimensional with unique nonzero element `κ_h`. -/
theorem map_eq_pair (hP : IsPlane W) (h : Dir W) :
    (W.map (lineMk h) : Set (LineSpace h)) = {0, hP.kappa h} := by
  ext x
  simp only [SetLike.mem_coe, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · intro hx
    by_cases hx0 : x = 0
    · exact Or.inl hx0
    · exact Or.inr (eq_kappa_of_ne_zero hP h hx hx0)
  · rintro (rfl | rfl)
    · exact Submodule.zero_mem _
    · exact kappa_mem_map hP h

/-! ## B4: the label formula -/

/-- The `h`-line of `Φ_W(m)` has quotient parameter `[m] + κ_h`. -/
theorem localFamily_apply (hP : IsPlane W) (m : Γ) (h : Dir W) :
    localFamily hP m h = lineMk h m + hP.kappa h := rfl

/-- Every even family admits a unique deleted point `m` realizing all its
labels in the affine form `[m] + κ`. -/
theorem existsUnique_label (hP : IsPlane W) {P : LineFamily W}
    (hE : IsEven P) :
    ∃! m : Γ, ∀ h : Dir W, P h = lineMk h m + hP.kappa h := by
  obtain ⟨m, hm⟩ := exists_localFamily_eq hP hE
  refine ⟨m, fun h => by rw [← hm]; rfl, ?_⟩
  intro m' hm'
  apply localFamily_injective hP
  rw [hm]
  funext h
  exact (hm' h).symm

end AffineCDC
