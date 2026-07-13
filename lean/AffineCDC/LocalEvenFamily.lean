import AffineCDC.Basic

/-!
# Local even families of affine lines

The key design decision of the slice: a two-point affine line of direction `h`
is *encoded by its class in the edge quotient* `Γ ⧸ ⟨h⟩`.  Over `𝔽₂` the cosets
of `span {h}` are literally the two-point sets `{p, p + h}` (see
`AffineCDC.OppositeFiber.coset_eq_pair`), so nothing is lost — and the
"parametrization of direction-`h` lines by `Γ/⟨h⟩`" that the paper spec derives
in Block 2 becomes primitive rather than derived.

A *line family* assigns to every direction `h` of `W` a line of direction `h`.
It is *even* when every point of `Γ` lies on an even number of the lines.
-/

namespace AffineCDC

variable {Γ : Type*} [AddCommGroup Γ] [Module (ZMod 2) Γ]
variable {W : Submodule (ZMod 2) Γ}

/-- The space of direction-`h` lines: the quotient of `Γ` by the direction. -/
abbrev LineSpace (h : Dir W) : Type _ := Γ ⧸ Submodule.span (ZMod 2) {(h : Γ)}

/-- The tautological parametrization of direction-`h` lines: `p ↦` the line
through `p`.  (A linear map, so `map_add` etc. apply.) -/
def lineMk (h : Dir W) : Γ →ₗ[ZMod 2] LineSpace h :=
  (Submodule.span (ZMod 2) {(h : Γ)}).mkQ

@[simp] lemma lineMk_self (h : Dir W) : lineMk h (h : Γ) = 0 :=
  (Submodule.Quotient.mk_eq_zero _).mpr (Submodule.mem_span_singleton_self _)

/-- Two points give the same direction-`h` line iff they agree or differ by `h`. -/
lemma lineMk_eq_iff {h : Dir W} {s p : Γ} :
    lineMk h s = lineMk h p ↔ s + p = 0 ∨ s + p = (h : Γ) := by
  show Submodule.Quotient.mk s = Submodule.Quotient.mk p ↔ _
  rw [Submodule.Quotient.eq, char2_sub, mem_span_singleton_char2]

/-- `lineMk h a` vanishes iff `a ∈ {0, h}`. -/
lemma lineMk_eq_zero_iff {h : Dir W} {a : Γ} :
    lineMk h a = 0 ↔ a = 0 ∨ a = (h : Γ) := by
  show Submodule.Quotient.mk a = 0 ↔ _
  rw [Submodule.Quotient.mk_eq_zero, mem_span_singleton_char2]

/-- A family of lines, one for each direction of `W`. -/
abbrev LineFamily (W : Submodule (ZMod 2) Γ) : Type _ :=
  (h : Dir W) → LineSpace h

/-- `P` covers the point `s` in direction `h`: `s` lies on the line `P h`. -/
def Covers (P : LineFamily W) (s : Γ) (h : Dir W) : Prop :=
  lineMk h s = P h

/-- The set of directions in which `P` covers `s`. -/
def coverSet (P : LineFamily W) (s : Γ) : Set (Dir W) :=
  {h | Covers P s h}

@[simp] lemma mem_coverSet {P : LineFamily W} {s : Γ} {h : Dir W} :
    h ∈ coverSet P s ↔ Covers P s h := Iff.rfl

/-- A line family is *even* when every point is covered an even number of
times.  (For a plane the count is `0` or `2`; the definition does not need to
know that.) -/
def IsEven (P : LineFamily W) : Prop :=
  ∀ s : Γ, Even (coverSet P s).ncard

/-- The local solution space: even families of lines. -/
def LocalEvenFamily (W : Submodule (ZMod 2) Γ) : Type _ :=
  {P : LineFamily W // IsEven P}

/-! ## Translation: `Γ` acts on line families -/

/-- Translate a line family by `a`: each line is translated by `a`. -/
def translate (a : Γ) (P : LineFamily W) : LineFamily W :=
  fun h => lineMk h a + P h

lemma covers_translate {a s : Γ} {P : LineFamily W} {h : Dir W} :
    Covers (translate a P) s h ↔ Covers P (s + a) h := by
  unfold Covers translate
  rw [map_add]
  constructor
  · intro e
    calc lineMk h s + lineMk h a
        = (lineMk h a + P h) + lineMk h a := by rw [← e]
      _ = P h := by
          rw [add_comm (lineMk h a) (P h), char2_add_cancel_right]
  · intro e
    calc lineMk h s
        = (lineMk h s + lineMk h a) + lineMk h a := by
          rw [char2_add_cancel_right]
      _ = lineMk h a + P h := by rw [e, add_comm]

/-- Evenness is translation-invariant. -/
lemma IsEven.translate {P : LineFamily W} (hE : IsEven P) (a : Γ) :
    IsEven (AffineCDC.translate a P) := by
  intro s
  have hs : coverSet (AffineCDC.translate a P) s = coverSet P (s + a) := by
    ext h
    simp only [mem_coverSet]
    exact covers_translate
  rw [hs]
  exact hE (s + a)

end AffineCDC
