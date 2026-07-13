import Mathlib

/-!
# Basics: characteristic two, directions, planes

Ground conventions for the AffineCDC development.

`Γ` is an arbitrary `ZMod 2`-module (an `𝔽₂`-vector space): we require neither
finiteness nor finite dimension of `Γ`.  A *plane* `W ≤ Γ` is a two-dimensional
subspace; its nonzero vectors (`Dir W`) are the three *directions* of the local
theory.  Rather than fixing an enumeration of the three directions — which the
paper spec forbids as non-mathematical data — we record the intrinsic Klein
structure of a plane as the `Prop`-valued `IsPlane`:

* there is a nonzero direction;
* every direction has a companion direction distinct from it;
* any three pairwise distinct directions satisfy `b = a + h`.

`IsPlane.of_finrank_eq_two` (in `AffineCDC.Rank`) shows the intrinsic structure
is implied by `finrank = 2`, so no generality is lost, while the main
development never touches bases, coordinates, or cardinality.
-/

namespace AffineCDC

variable {Γ : Type*} [AddCommGroup Γ] [Module (ZMod 2) Γ]

/-! ## Characteristic-two arithmetic -/

@[simp] lemma char2_add_self (x : Γ) : x + x = 0 := by
  have h := two_smul (ZMod 2) x
  rwa [show (2 : ZMod 2) = 0 by decide, zero_smul, eq_comm] at h

lemma char2_add_eq_zero_iff {x y : Γ} : x + y = 0 ↔ x = y := by
  constructor
  · intro h
    have h' := congrArg (· + y) h
    simpa [add_assoc] using h'
  · rintro rfl
    exact char2_add_self _

@[simp] lemma char2_neg (x : Γ) : -x = x :=
  neg_eq_of_add_eq_zero_left (char2_add_self x)

@[simp] lemma char2_sub (x y : Γ) : x - y = x + y := by
  rw [sub_eq_add_neg, char2_neg]

@[simp] lemma char2_add_cancel_right (x a : Γ) : x + a + a = x := by
  rw [add_assoc, char2_add_self, add_zero]

@[simp] lemma char2_add_left_eq (x y : Γ) : x + (x + y) = y := by
  rw [← add_assoc, char2_add_self, zero_add]

/-- `x + a = c ↔ x = c + a`: addition is its own inverse. -/
lemma char2_add_eq_iff {x a c : Γ} : x + a = c ↔ x = c + a :=
  ⟨fun e => by rw [← e, char2_add_cancel_right],
   fun e => by rw [e, char2_add_cancel_right]⟩

/-- Over `𝔽₂` the span of a single vector is just `{0, h}`. -/
lemma mem_span_singleton_char2 {x h : Γ} :
    x ∈ Submodule.span (ZMod 2) {h} ↔ x = 0 ∨ x = h := by
  rw [Submodule.mem_span_singleton]
  constructor
  · rintro ⟨c, rfl⟩
    have hc : c = 0 ∨ c = 1 := by revert c; decide
    rcases hc with rfl | rfl
    · exact Or.inl (zero_smul _ h)
    · exact Or.inr (one_smul _ h)
  · rintro (rfl | rfl)
    · exact ⟨0, zero_smul _ h⟩
    · exact ⟨1, one_smul _ _⟩

/-! ## Directions of a subspace -/

/-- A *direction* of `W` is a nonzero vector of `W`.  For a plane there are
exactly three, but we never enumerate them. -/
abbrev Dir (W : Submodule (ZMod 2) Γ) : Type _ := {h : Γ // h ∈ W ∧ h ≠ 0}

namespace Dir

variable {W : Submodule (ZMod 2) Γ}

lemma coe_mem (h : Dir W) : (h : Γ) ∈ W := h.2.1

lemma coe_ne_zero (h : Dir W) : (h : Γ) ≠ 0 := h.2.2

/-- The sum of two distinct directions is a direction (characteristic two:
`a + h = 0` would force `a = h`). -/
def add (h a : Dir W) (hne : (a : Γ) ≠ (h : Γ)) : Dir W :=
  ⟨(a : Γ) + (h : Γ), W.add_mem a.coe_mem h.coe_mem,
   fun h0 => hne (char2_add_eq_zero_iff.mp h0)⟩

@[simp] lemma add_coe (h a : Dir W) (hne : (a : Γ) ≠ (h : Γ)) :
    (Dir.add h a hne : Γ) = (a : Γ) + (h : Γ) := rfl

end Dir

/-! ## Planes -/

/-- The intrinsic structure of a two-dimensional subspace over `𝔽₂`, phrased
without choosing coordinates: the three directions form a Klein triple. -/
structure IsPlane (W : Submodule (ZMod 2) Γ) : Prop where
  /-- There is at least one direction. -/
  nonempty : ∃ h : Γ, h ∈ W ∧ h ≠ 0
  /-- Every direction has a companion distinct from it. -/
  exists_ne : ∀ h : Dir W, ∃ a : Dir W, (a : Γ) ≠ (h : Γ)
  /-- Any three pairwise distinct directions are additively dependent. -/
  eq_add_of_ne : ∀ h a b : Dir W, (a : Γ) ≠ (h : Γ) → (b : Γ) ≠ (h : Γ) →
    (a : Γ) ≠ (b : Γ) → (b : Γ) = (a : Γ) + (h : Γ)

namespace IsPlane

variable {W : Submodule (ZMod 2) Γ} (hP : IsPlane W)

include hP

/-- A chosen direction of the plane (any one; nothing depends on the choice). -/
noncomputable def dir₀ : Dir W := ⟨hP.nonempty.choose, hP.nonempty.choose_spec⟩

/-- A chosen companion direction of `h` (any one; nothing depends on the choice). -/
noncomputable def other (h : Dir W) : Dir W := (hP.exists_ne h).choose

lemma other_ne (h : Dir W) : (hP.other h : Γ) ≠ (h : Γ) :=
  (hP.exists_ne h).choose_spec

/-- Every direction is `x`, `y`, or `x + y`. -/
lemma trichotomy (x y : Dir W) (hyx : (y : Γ) ≠ (x : Γ)) (h : Dir W) :
    h = x ∨ h = y ∨ (h : Γ) = (x : Γ) + (y : Γ) := by
  by_cases h1 : h = x
  · exact Or.inl h1
  by_cases h2 : h = y
  · exact Or.inr (Or.inl h2)
  have hvx : (h : Γ) ≠ (x : Γ) := fun e => h1 (Subtype.ext e)
  have hvy : (y : Γ) ≠ (h : Γ) := fun e => h2 (Subtype.ext e.symm)
  have := hP.eq_add_of_ne x y h hyx hvx hvy
  exact Or.inr (Or.inr (this.trans (add_comm _ _)))

/-- The directions other than `d` are exactly the pair
`{other d, other d + d}`. -/
lemma compl_eq_pair (d : Dir W) :
    {h : Dir W | h ≠ d} =
      {hP.other d, Dir.add d (hP.other d) (hP.other_ne d)} := by
  ext h
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · intro hne
    rcases hP.trichotomy d (hP.other d) (hP.other_ne d) h with h1 | h2 | h3
    · exact absurd h1 hne
    · exact Or.inl h2
    · refine Or.inr (Subtype.ext ?_)
      rw [h3, Dir.add_coe, add_comm]
  · rintro (rfl | rfl)
    · exact fun e => hP.other_ne d (congrArg Subtype.val e)
    · intro e
      have := congrArg Subtype.val e
      rw [Dir.add_coe] at this
      exact (hP.other d).coe_ne_zero
        (add_right_cancel (a := (hP.other d : Γ)) (b := (d : Γ)) (c := 0)
          (by rw [zero_add]; exact this))

/-- There are exactly two directions other than `d`. -/
lemma ncard_compl (d : Dir W) : {h : Dir W | h ≠ d}.ncard = 2 := by
  rw [hP.compl_eq_pair d]
  refine Set.ncard_pair fun e => ?_
  have := congrArg Subtype.val e
  rw [Dir.add_coe] at this
  exact d.coe_ne_zero (add_left_cancel (a := (hP.other d : Γ)) (b := (0 : Γ))
    (by rw [add_zero]; exact this)).symm

end IsPlane

end AffineCDC
