import AffineCDC.LocalClassification

/-!
# Internalized comparison: the slot construction is a gauge choice

The original manuscript (eq. (2)–(3)) builds the local assignment from an
*ordering* of the three directions and a base parameter `t`: with slots
`(a, b, c)` and `x = f(a)`, it assigns base point `t` to the outer slots and
`t + x` to the middle slot (`slotFamily`).

`slotFamily_eq_localFamily` shows this equals `Φ_W(t + y)` where `y` is the
*middle* direction — so the slot data is exactly a gauge choice, with the
explicit dictionary

`m⁰ = t + f(b)`

between the manuscript's `t`-parameter and our deleted point.  Combined with
the gauge classification (T4 C1), the manuscript's right-hand side `d` and
the natural class `c_f` are gauge-equivalent, which is the formal content of
"equivalent reconstruction" — internalized, with no reference to external
code.
-/

namespace AffineCDC

variable {Γ : Type*} [AddCommGroup Γ] [Module (ZMod 2) Γ]
variable {W : Submodule (ZMod 2) Γ}

open Classical in
/-- The manuscript's slot assignment: ordered directions `(x, y, ·)`, base
point `t` on the outer slots, `t + x` on the middle slot `y`. -/
noncomputable def slotFamily (x y : Dir W) (t : Γ) : LineFamily W :=
  fun h => if h = y then lineMk h (t + (x : Γ)) else lineMk h t

/-- **Internalization**: the slot assignment is the local family with
deleted point `t + y` — slot data is a gauge choice, and the manuscript's
parameter `t` differs from the deleted point by the middle direction. -/
theorem slotFamily_eq_localFamily (hP : IsPlane W) {x y z : Dir W}
    (hs : (x : Γ) + (y : Γ) + (z : Γ) = 0) (t : Γ) :
    slotFamily x y t = localFamily hP (t + (y : Γ)) := by
  -- distinctness facts from the sum-zero triple
  have hyx : (y : Γ) ≠ (x : Γ) := by
    intro e
    apply z.coe_ne_zero
    rw [e, char2_add_self, zero_add] at hs
    exact hs
  have hxy : (x : Γ) ≠ (y : Γ) := fun e => hyx e.symm
  funext h
  unfold slotFamily
  rcases hP.trichotomy x y hyx h with h1 | h1 | h1
  · -- outer slot `x`
    rw [h1, if_neg (fun e => hxy (congrArg Subtype.val e)),
      show localFamily hP (t + (y : Γ)) x
        = lineMk x (t + (y : Γ)) + hP.kappa x from rfl,
      hP.kappa_eq x y hyx, ← map_add, char2_add_cancel_right]
  · -- middle slot `y`
    have harg : t + (y : Γ) + (x : Γ) = (t + (x : Γ)) + (y : Γ) := by
      rw [add_assoc, add_comm (y : Γ) (x : Γ), ← add_assoc]
    rw [h1, if_pos rfl,
      show localFamily hP (t + (y : Γ)) y
        = lineMk y (t + (y : Γ)) + hP.kappa y from rfl,
      hP.kappa_eq y x hxy, ← map_add, harg, lineMk_eq_iff]
    right
    exact char2_add_left_eq _ _
  · -- outer slot `z` (the direction with `↑h = ↑x + ↑y`)
    have hhy : h ≠ y := by
      intro e
      apply x.coe_ne_zero
      rw [e] at h1
      exact (add_right_cancel (a := (x : Γ)) (b := (y : Γ)) (c := (0 : Γ))
        (by rw [zero_add]; exact h1.symm))
    have hxh : (x : Γ) ≠ (h : Γ) := by
      intro e
      apply y.coe_ne_zero
      rw [← e] at h1
      exact (add_left_cancel (a := (x : Γ)) (b := (0 : Γ)) (c := (y : Γ))
        (by rw [add_zero]; exact h1)).symm
    have harg : t + (y : Γ) + (x : Γ) = t + (h : Γ) := by
      rw [add_assoc, add_comm (y : Γ) (x : Γ), ← h1]
    rw [if_neg hhy,
      show localFamily hP (t + (y : Γ)) h
        = lineMk h (t + (y : Γ)) + hP.kappa h from rfl,
      hP.kappa_eq h x hxh, ← map_add, harg, lineMk_eq_iff]
    right
    exact char2_add_left_eq _ _

end AffineCDC
