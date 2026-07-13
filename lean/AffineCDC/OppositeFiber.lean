import AffineCDC.LocalClassification

/-!
# Opposite-fibre characterization (Corollary A3)

The coset encoding of lines is reconciled with the two-point-set picture:

* `coset_eq_pair`: the set of points on the direction-`h` line through `p`
  is exactly `{p, p + h}` — so nothing was lost by taking `Γ/⟨h⟩` as the
  primitive notion of "line";
* `localFamily_points_pair`: the line `Φ_W(m) h` is the two-point set
  `{m + a, m + a + h}` where `a` is either direction other than `h` —
  the original "deleted-line" description `(m + W) ∖ {m, m + h}`;
* `localFamily_points`: precisely that description, as a set identity;
* `not_covers_self`: `m` does not lie on `Φ_W(m) h` — combined with
  `coset_eq_pair` this is the opposite-fibre statement: among the two fibres
  of `m + W → (m + W)/⟨h⟩`, the line `Φ_W(m) h` is the one *not* containing
  `m`.
-/

namespace AffineCDC

variable {Γ : Type*} [AddCommGroup Γ] [Module (ZMod 2) Γ]
variable {W : Submodule (ZMod 2) Γ}

/-- The points of the direction-`h` line through `p` are exactly `{p, p + h}`:
cosets of `⟨h⟩` and two-point sets of difference `h` are the same thing. -/
theorem coset_eq_pair (h : Dir W) (p : Γ) :
    {s : Γ | lineMk h s = lineMk h p} = {p, p + (h : Γ)} := by
  ext s
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff,
    lineMk_eq_iff]
  constructor
  · rintro (e | e)
    · exact Or.inl (char2_add_eq_zero_iff.mp e)
    · exact Or.inr (by rw [char2_add_eq_iff.mp e, add_comm])
  · rintro (rfl | rfl)
    · exact Or.inl (char2_add_self _)
    · right
      rw [add_comm p (h : Γ), char2_add_cancel_right]

/-- The line `Φ_W(m) h` passes through `m + a` for every direction `a ≠ h`. -/
lemma localFamily_apply_eq (hP : IsPlane W) (m : Γ) (h a : Dir W)
    (ha : (a : Γ) ≠ (h : Γ)) :
    localFamily hP m h = lineMk h (m + (a : Γ)) := by
  show lineMk h m + hP.kappa h = _
  rw [hP.kappa_eq h a ha, map_add]

/-- Two-point description: `Φ_W(m) h = {m + a, m + a + h}` for either
direction `a ≠ h`. -/
theorem localFamily_points_pair (hP : IsPlane W) (m : Γ) (h a : Dir W)
    (ha : (a : Γ) ≠ (h : Γ)) :
    {s : Γ | lineMk h s = localFamily hP m h}
      = {m + (a : Γ), m + (a : Γ) + (h : Γ)} := by
  rw [localFamily_apply_eq hP m h a ha, coset_eq_pair]

/-- **Corollary A3** (deleted-line description): the points of `Φ_W(m) h` are
exactly `(m + W) ∖ {m, m + h}`. -/
theorem localFamily_points (hP : IsPlane W) (m : Γ) (h : Dir W) :
    {s : Γ | lineMk h s = localFamily hP m h}
      = ((m + ·) '' (W : Set Γ)) \ {m, m + (h : Γ)} := by
  ext s
  simp only [Set.mem_setOf_eq, Set.mem_sdiff, Set.mem_image, SetLike.mem_coe,
    Set.mem_insert_iff, Set.mem_singleton_iff]
  rw [show (lineMk h s = localFamily hP m h)
      = Covers (localFamily hP m) s h from rfl, covers_localFamily_iff]
  constructor
  · rintro ⟨hmem, h0, hh⟩
    refine ⟨⟨s + m, hmem, ?_⟩, ?_⟩
    · rw [add_comm s m, char2_add_left_eq]
    · rintro (rfl | rfl)
      · exact h0 (char2_add_self _)
      · apply hh
        rw [add_comm m (h : Γ), add_assoc, char2_add_self, add_zero]
  · rintro ⟨⟨w, hw, rfl⟩, hne⟩
    have hne1 : m + w ≠ m := fun e => hne (Or.inl e)
    have hne2 : m + w ≠ m + (h : Γ) := fun e => hne (Or.inr e)
    have hwsm : m + w + m = w := by
      rw [add_comm m w, add_assoc, char2_add_self, add_zero]
    refine ⟨by rw [hwsm]; exact hw, ?_, ?_⟩
    · rw [hwsm]
      rintro rfl
      exact hne1 (add_zero m)
    · rw [hwsm]
      rintro rfl
      exact hne2 rfl

/-- `m` itself does not lie on `Φ_W(m) h`: the line is the fibre of
`m + W → (m + W)/⟨h⟩` *opposite* to `m`. -/
theorem not_covers_self (hP : IsPlane W) (m : Γ) (h : Dir W) :
    ¬ Covers (localFamily hP m) m h := by
  rw [covers_localFamily_iff]
  rintro ⟨-, h0, -⟩
  exact h0 (char2_add_self m)

end AffineCDC
