import AffineCDC.LocalEvenFamily

/-!
# Local classification (Theorem A)

Every even family of lines is `Φ_W(m)` for a unique deleted point `m ∈ Γ`:

* `localFamily hP m` is `Φ_W(m)`, defined coordinate-freely as
  `h ↦ [m] + κ h`, where `κ h` is the common class in `Γ/⟨h⟩` of the other two
  directions (`IsPlane.kappa`);
* `covers_localFamily_iff` is the master computation:
  `Φ_W(m)` covers `s` in direction `h` iff `s + m ∈ W ∖ {0, h}`;
* `isEven_localFamily`, `localFamily_injective`, `exists_localFamily_eq`
  assemble to the bijection `localEquiv : Γ ≃ LocalEvenFamily W`;
* `localFamily_translate` is the torsor equivariance
  `Φ_W(m + a) = a ⋅ Φ_W(m)` (the content of Corollary A1).

No ordering of the three directions, no finiteness of `Γ`, no choice enters
any statement; the choices inside `kappa` are proved immaterial by
`IsPlane.kappa_eq`.
-/

namespace AffineCDC

variable {Γ : Type*} [AddCommGroup Γ] [Module (ZMod 2) Γ]
variable {W : Submodule (ZMod 2) Γ}

namespace IsPlane

variable (hP : IsPlane W)

/-- `κ h`: the common class in `Γ/⟨h⟩` of the two directions other than `h`.
Defined via the chosen companion; `kappa_eq` shows independence of the choice. -/
noncomputable def kappa (h : Dir W) : LineSpace h :=
  lineMk h (hP.other h : Γ)

lemma kappa_def (h : Dir W) : hP.kappa h = lineMk h (hP.other h : Γ) := rfl

/-- `κ h` is the class of *any* direction other than `h`. -/
lemma kappa_eq (h a : Dir W) (ha : (a : Γ) ≠ (h : Γ)) :
    hP.kappa h = lineMk h (a : Γ) := by
  rw [kappa_def, lineMk_eq_iff]
  by_cases hoa : (hP.other h : Γ) = (a : Γ)
  · exact Or.inl (char2_add_eq_zero_iff.mpr hoa)
  · right
    have hb := hP.eq_add_of_ne h (hP.other h) a (hP.other_ne h) ha hoa
    rw [hb, char2_add_left_eq]

/-- `κ h ≠ 0`: the other directions do not lie on `⟨h⟩`. -/
lemma kappa_ne_zero (h : Dir W) : hP.kappa h ≠ 0 := by
  rw [kappa_def]
  intro h0
  rw [lineMk_eq_zero_iff] at h0
  rcases h0 with h0 | h0
  · exact (hP.other h).coe_ne_zero h0
  · exact hP.other_ne h h0

end IsPlane

/-- `Φ_W(m)`: the local even family with deleted point `m`. -/
noncomputable def localFamily (hP : IsPlane W) (m : Γ) : LineFamily W :=
  fun h => lineMk h m + hP.kappa h

/-- Master computation: `Φ_W(m)` covers `s` in direction `h` iff
`s + m ∈ W ∖ {0, h}` — i.e. iff `s - m` is a direction other than `h`. -/
lemma covers_localFamily_iff {hP : IsPlane W} {m s : Γ} {h : Dir W} :
    Covers (localFamily hP m) s h ↔
      s + m ∈ W ∧ s + m ≠ 0 ∧ s + m ≠ (h : Γ) := by
  unfold Covers localFamily
  rw [hP.kappa_def, ← map_add, lineMk_eq_iff, ← add_assoc]
  constructor
  · rintro (e | e)
    · have hsm : s + m = (hP.other h : Γ) := char2_add_eq_zero_iff.mp e
      rw [hsm]
      exact ⟨(hP.other h).coe_mem, (hP.other h).coe_ne_zero, hP.other_ne h⟩
    · have hsm : s + m = (h : Γ) + (hP.other h : Γ) := char2_add_eq_iff.mp e
      rw [hsm]
      refine ⟨W.add_mem h.coe_mem (hP.other h).coe_mem, ?_, ?_⟩
      · intro e0
        exact hP.other_ne h (char2_add_eq_zero_iff.mp e0).symm
      · intro e0
        exact (hP.other h).coe_ne_zero
          (add_left_cancel (a := (h : Γ)) (b := (hP.other h : Γ)) (c := 0)
            (by rw [add_zero]; exact e0))
  · rintro ⟨hmem, h0, hh⟩
    by_cases hcase : s + m = (hP.other h : Γ)
    · exact Or.inl (char2_add_eq_zero_iff.mpr hcase)
    · right
      have hd := hP.eq_add_of_ne h (hP.other h) ⟨s + m, hmem, h0⟩
        (hP.other_ne h) hh (fun e => hcase e.symm)
      show s + m + (hP.other h : Γ) = (h : Γ)
      rw [show s + m = (hP.other h : Γ) + (h : Γ) from hd,
        add_comm (hP.other h : Γ) (h : Γ), char2_add_cancel_right]

/-- `Φ_W(m)` is even: each point is covered `0` or `2` times. -/
theorem isEven_localFamily (hP : IsPlane W) (m : Γ) :
    IsEven (localFamily hP m) := by
  intro s
  by_cases hc : s + m ∈ W ∧ s + m ≠ 0
  · have hs : coverSet (localFamily hP m) s
        = {h : Dir W | h ≠ (⟨s + m, hc.1, hc.2⟩ : Dir W)} := by
      ext h
      simp only [mem_coverSet, Set.mem_setOf_eq, covers_localFamily_iff]
      constructor
      · rintro ⟨-, -, hne⟩ e
        exact hne (by rw [e])
      · intro hne
        exact ⟨hc.1, hc.2, fun e => hne (Subtype.ext e.symm)⟩
    rw [hs, hP.ncard_compl]
    exact even_two
  · have hs : coverSet (localFamily hP m) s = ∅ := by
      ext h
      simp only [mem_coverSet, covers_localFamily_iff, Set.mem_empty_iff_false,
        iff_false, not_and]
      intro hmem h0
      exact absurd ⟨hmem, h0⟩ hc
    rw [hs, Set.ncard_empty]
    exact ⟨0, rfl⟩

/-- Injectivity: the deleted point is determined by the family. -/
theorem localFamily_injective (hP : IsPlane W) :
    Function.Injective (localFamily hP) := by
  intro m m' hmm'
  have key : ∀ h : Dir W, m + m' = 0 ∨ m + m' = (h : Γ) := by
    intro h
    have e := congrFun hmm' h
    unfold localFamily at e
    exact lineMk_eq_iff.mp (add_right_cancel e)
  by_cases h0 : m + m' = 0
  · exact char2_add_eq_zero_iff.mp h0
  · exfalso
    have hx := (key hP.dir₀).resolve_left h0
    have hy := (key (hP.other hP.dir₀)).resolve_left h0
    exact hP.other_ne hP.dir₀ (hy.symm.trans hx)

/-- Parity step: if an even family covers `s` in direction `x`, then it covers
`s` in exactly one of the two other directions `y`, `z = x + y`. -/
lemma covers_parity (hP : IsPlane W) {P : LineFamily W} (hE : IsEven P)
    (s : Γ) (x y z : Dir W) (hyx : (y : Γ) ≠ (x : Γ))
    (hz : (z : Γ) = (x : Γ) + (y : Γ)) (hx : Covers P s x) :
    Covers P s y ↔ ¬ Covers P s z := by
  have hE' := hE s
  have hxy : x ≠ y := fun e => hyx (congrArg Subtype.val e.symm)
  have hzx : z ≠ x := by
    intro e
    apply y.coe_ne_zero
    have e' : (x : Γ) + (y : Γ) = (x : Γ) := by rw [← hz, e]
    exact add_left_cancel (a := (x : Γ)) (b := (y : Γ)) (c := 0)
      (by rw [add_zero]; exact e')
  have hzy : z ≠ y := by
    intro e
    apply x.coe_ne_zero
    have e' : (x : Γ) + (y : Γ) = (y : Γ) := by rw [← hz, e]
    exact add_right_cancel (a := (x : Γ)) (b := (y : Γ)) (c := (0 : Γ))
      (by rw [zero_add]; exact e')
  have tri : ∀ h : Dir W, h = x ∨ h = y ∨ h = z := by
    intro h
    rcases hP.trichotomy x y hyx h with h1 | h1 | h1
    · exact Or.inl h1
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr (Subtype.ext (h1.trans hz.symm)))
  constructor
  · intro hy hzc
    have hset : coverSet P s = {x, y, z} := by
      ext h
      simp only [mem_coverSet, Set.mem_insert_iff, Set.mem_singleton_iff]
      constructor
      · intro _; exact tri h
      · rintro (rfl | rfl | rfl)
        · exact hx
        · exact hy
        · exact hzc
    rw [hset] at hE'
    have hcard : ({x, y, z} : Set (Dir W)).ncard = 3 := by
      rw [Set.ncard_insert_of_notMem
          (by simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
              exact fun h => h.elim hxy hzx.symm)
          ((Set.finite_singleton z).insert y),
        Set.ncard_pair (Ne.symm hzy)]
    rw [hcard] at hE'
    exact absurd hE' (by decide)
  · intro hnz
    by_contra hny
    have hset : coverSet P s = {x} := by
      ext h
      simp only [mem_coverSet, Set.mem_singleton_iff]
      constructor
      · intro hh
        rcases tri h with rfl | rfl | rfl
        · rfl
        · exact absurd hh hny
        · exact absurd hh hnz
      · rintro rfl; exact hx
    rw [hset, Set.ncard_singleton] at hE'
    exact absurd hE' (by decide)

/-- Surjectivity: every even family has a deleted point. -/
theorem exists_localFamily_eq (hP : IsPlane W) {P : LineFamily W}
    (hE : IsEven P) : ∃ m : Γ, localFamily hP m = P := by
  -- Name the three directions.  (No ordering is *used*: `covers_parity` and
  -- the coordinate computations below are symmetric in the roles.)
  set x : Dir W := hP.dir₀
  set y : Dir W := hP.other x
  have hyx : (y : Γ) ≠ (x : Γ) := hP.other_ne x
  set z : Dir W := Dir.add x y hyx with hzdef
  have hzval : (z : Γ) = (y : Γ) + (x : Γ) := by rw [hzdef, Dir.add_coe]
  have hzsum : (z : Γ) = (x : Γ) + (y : Γ) := by rw [hzval, add_comm]
  have hzy : (z : Γ) ≠ (y : Γ) := by
    rw [hzval]
    intro e
    exact x.coe_ne_zero (add_left_cancel (a := (y : Γ)) (b := (x : Γ)) (c := 0)
      (by rw [add_zero]; exact e))
  -- A representative point of the line `P x`.
  obtain ⟨p, hp⟩ := Submodule.Quotient.mk_surjective _ (P x)
  have hpx : Covers P p x := hp
  -- `q = p + x` is covered in direction `x`.
  have hqx : Covers P (p + (x : Γ)) x := by
    show lineMk x (p + (x : Γ)) = P x
    rw [map_add, lineMk_self, add_zero]
    exact hpx
  -- The image of `x` is nonzero in the quotients by the other directions.
  have hxy_line : lineMk y (x : Γ) ≠ 0 := by
    intro e
    rw [lineMk_eq_zero_iff] at e
    rcases e with e | e
    · exact x.coe_ne_zero e
    · exact hyx e.symm
  have hxz_line : lineMk z (x : Γ) ≠ 0 := by
    intro e
    rw [lineMk_eq_zero_iff] at e
    rcases e with e | e
    · exact x.coe_ne_zero e
    · rw [hzval] at e
      exact y.coe_ne_zero (add_right_cancel (a := (y : Γ)) (b := (x : Γ))
        (c := (0 : Γ)) (by rw [zero_add]; exact e.symm))
  -- Group identities used to normalize the arguments of `lineMk`.
  have hargA : p + (z : Γ) + (y : Γ) = p + (x : Γ) := by
    rw [hzval, add_assoc p, add_comm ((y : Γ) + (x : Γ)) (y : Γ),
      char2_add_left_eq]
  have hargZ : ∀ w : Γ, p + w + w = p := fun w => char2_add_cancel_right p w
  have hargB : p + (y : Γ) + (x : Γ) = p + (x : Γ) + (y : Γ) := by
    rw [add_assoc p, add_comm (y : Γ) (x : Γ), ← add_assoc p]
  by_cases hpy : Covers P p y
  · -- Case A: `P` covers `p` in directions `x` and `y`; delete `m = p + z`.
    -- `q = p + x` is covered in `x` but not `y`, hence in `z`.
    have hqy : ¬ Covers P (p + (x : Γ)) y := by
      show ¬ lineMk y (p + (x : Γ)) = P y
      rw [map_add]
      intro e
      have e2 : lineMk y p + 0 = lineMk y p + lineMk y (x : Γ) := by
        rw [add_zero, e]
        exact hpy
      exact hxy_line (add_left_cancel e2).symm
    have hqz : Covers P (p + (x : Γ)) z := by
      by_contra hqz
      exact hqy
        ((covers_parity hP hE (p + (x : Γ)) x y z hyx hzsum hqx).mpr hqz)
    refine ⟨p + (z : Γ), funext fun h => ?_⟩
    show lineMk h (p + (z : Γ)) + hP.kappa h = P h
    rcases hP.trichotomy x y hyx h with h1 | h1 | h1
    · -- direction `x`
      rw [h1, hP.kappa_eq x y hyx, ← map_add, hargA, map_add, lineMk_self,
        add_zero]
      exact hpx
    · -- direction `y`
      rw [h1, hP.kappa_eq y z hzy, ← map_add, hargZ]
      exact hpy
    · -- direction `z`
      have hhz : h = z := Subtype.ext (h1.trans hzsum.symm)
      rw [hhz, hP.kappa_eq z y (Ne.symm hzy), ← map_add, hargA]
      exact hqz
  · -- Case B: `P` covers `p` in directions `x` and `z`; delete `m = p + y`.
    have hpz : Covers P p z := by
      by_contra hpz
      exact hpy ((covers_parity hP hE p x y z hyx hzsum hpx).mpr hpz)
    have hqz : ¬ Covers P (p + (x : Γ)) z := by
      show ¬ lineMk z (p + (x : Γ)) = P z
      rw [map_add]
      intro e
      have e2 : lineMk z p + 0 = lineMk z p + lineMk z (x : Γ) := by
        rw [add_zero, e]
        exact hpz
      exact hxz_line (add_left_cancel e2).symm
    have hqy : Covers P (p + (x : Γ)) y :=
      (covers_parity hP hE (p + (x : Γ)) x y z hyx hzsum hqx).mpr hqz
    refine ⟨p + (y : Γ), funext fun h => ?_⟩
    show lineMk h (p + (y : Γ)) + hP.kappa h = P h
    rcases hP.trichotomy x y hyx h with h1 | h1 | h1
    · -- direction `x`
      rw [h1, hP.kappa_eq x y hyx, ← map_add, hargZ]
      exact hpx
    · -- direction `y`
      rw [h1, hP.kappa_eq y x (fun e => hyx e.symm), ← map_add, hargB,
        map_add, lineMk_self, add_zero]
      exact hqy
    · -- direction `z`
      have hhz : h = z := Subtype.ext (h1.trans hzsum.symm)
      rw [hhz, hP.kappa_eq z y (Ne.symm hzy), ← map_add, hargZ]
      exact hpz

/-- **Theorem A** (local classification): the deleted-point map is a bijection
from `Γ` onto the even families. -/
noncomputable def localEquiv (hP : IsPlane W) : Γ ≃ LocalEvenFamily W :=
  Equiv.ofBijective
    (fun m => ⟨localFamily hP m, isEven_localFamily hP m⟩)
    ⟨fun _ _ e => localFamily_injective hP (congrArg Subtype.val e),
     fun P => (exists_localFamily_eq hP P.2).imp fun _ hm => Subtype.ext hm⟩

/-- **Corollary A1** (torsor equivariance): `Φ_W(m + a) = a ⋅ Φ_W(m)`.
Together with `localEquiv` this exhibits `LocalEvenFamily W` as a `Γ`-torsor
and `Φ_W` as an equivariant (affine) isomorphism. -/
lemma localFamily_translate (hP : IsPlane W) (m a : Γ) :
    localFamily hP (m + a) = translate a (localFamily hP m) := by
  funext h
  show lineMk h (m + a) + hP.kappa h = lineMk h a + (lineMk h m + hP.kappa h)
  rw [map_add]
  abel

end AffineCDC
