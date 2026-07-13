import AffineCDC.LocalClassification

/-!
# Naturality (Corollary A2)

A linear isomorphism `T : Γ ≃ₗ Γ'` carries the whole local theory of a plane
`W ≤ Γ` to that of `W.map T ≤ Γ'`:

* directions transport (`Dir.map` / `Dir.comap`, mutually inverse);
* line spaces transport (`lineEquivAt`, the quotient equivalence
  `Γ/⟨h⟩ ≃ Γ'/⟨T h⟩`);
* line families transport (`mapFamily`), preserving evenness (`IsEven.map`);
* planes transport (`IsPlane.map`);
* and the classification commutes with all of it
  (`mapFamily_localFamily` / `localEquiv_naturality`):

  `T_* (Φ_W(m)) = Φ_{T W}(T m)`.

Since none of the structure maps depends on an enumeration of the directions,
this is the precise statement that the local theory — in particular the
original proof's edge orderings — carries no coordinate content.
-/

namespace AffineCDC

variable {Γ Γ' : Type*} [AddCommGroup Γ] [Module (ZMod 2) Γ]
  [AddCommGroup Γ'] [Module (ZMod 2) Γ']
variable (T : Γ ≃ₗ[ZMod 2] Γ') {W : Submodule (ZMod 2) Γ}

/-! ## Transport of directions -/

/-- Push a direction of `W` forward along `T`. -/
def Dir.map (h : Dir W) : Dir (W.map (T : Γ →ₗ[ZMod 2] Γ')) :=
  ⟨T (h : Γ), Submodule.mem_map_of_mem h.coe_mem,
   fun e0 => h.coe_ne_zero (T.map_eq_zero_iff.mp e0)⟩

@[simp] lemma Dir.map_coe (h : Dir W) : (Dir.map T h : Γ') = T (h : Γ) := rfl

/-- Pull a direction of `W.map T` back along `T`. -/
def Dir.comap (h' : Dir (W.map (T : Γ →ₗ[ZMod 2] Γ'))) : Dir W :=
  ⟨T.symm (h' : Γ'), by
      have h1 := h'.coe_mem
      rw [Submodule.mem_map_equiv] at h1
      exact h1,
   fun e0 => h'.coe_ne_zero (T.symm.map_eq_zero_iff.mp e0)⟩

@[simp] lemma Dir.comap_coe (h' : Dir (W.map (T : Γ →ₗ[ZMod 2] Γ'))) :
    (Dir.comap T h' : Γ) = T.symm (h' : Γ') := rfl

@[simp] lemma Dir.map_comap (h' : Dir (W.map (T : Γ →ₗ[ZMod 2] Γ'))) :
    Dir.map T (Dir.comap T h') = h' :=
  Subtype.ext (T.apply_symm_apply _)

@[simp] lemma Dir.comap_map (h : Dir W) : Dir.comap T (Dir.map T h) = h :=
  Subtype.ext (T.symm_apply_apply _)

lemma Dir.map_injective : Function.Injective (Dir.map T (W := W)) :=
  fun _ _ e => Subtype.ext (T.injective (congrArg Subtype.val e))

/-! ## Transport of line spaces -/

/-- The quotient equivalence `Γ/⟨h⟩ ≃ Γ'/⟨h'⟩` induced by `T` when
`h' = T h`.  (The target direction is a parameter so that the equivalence
lands in the syntactically correct line space.) -/
def lineEquivAt (h : Dir W) (h' : Dir (W.map (T : Γ →ₗ[ZMod 2] Γ')))
    (hh : (h' : Γ') = T (h : Γ)) : LineSpace h ≃ₗ[ZMod 2] LineSpace h' :=
  Submodule.Quotient.equiv _ _ T
    (by rw [Submodule.map_span]; simp [hh])

@[simp] lemma lineEquivAt_lineMk (h : Dir W)
    (h' : Dir (W.map (T : Γ →ₗ[ZMod 2] Γ'))) (hh : (h' : Γ') = T (h : Γ))
    (s : Γ) : lineEquivAt T h h' hh (lineMk h s) = lineMk h' (T s) := by
  simp [lineEquivAt, lineMk, Submodule.mkQ_apply, Submodule.Quotient.equiv_apply,
    Submodule.mapQ_apply]

/-! ## Transport of line families -/

/-- Push a line family forward along `T`. -/
def mapFamily (P : LineFamily W) :
    LineFamily (W.map (T : Γ →ₗ[ZMod 2] Γ')) :=
  fun h' =>
    lineEquivAt T (Dir.comap T h') h' (T.apply_symm_apply (h' : Γ')).symm
      (P (Dir.comap T h'))

lemma covers_mapFamily {P : LineFamily W} {s' : Γ'}
    {h' : Dir (W.map (T : Γ →ₗ[ZMod 2] Γ'))} :
    Covers (mapFamily T P) s' h' ↔ Covers P (T.symm s') (Dir.comap T h') := by
  unfold Covers mapFamily
  have key : lineMk h' s'
      = lineEquivAt T (Dir.comap T h') h' (T.apply_symm_apply (h' : Γ')).symm
          (lineMk (Dir.comap T h') (T.symm s')) := by
    rw [lineEquivAt_lineMk, T.apply_symm_apply]
  rw [key]
  exact (lineEquivAt T (Dir.comap T h') h' _).injective.eq_iff

lemma coverSet_mapFamily (P : LineFamily W) (s' : Γ') :
    coverSet (mapFamily T P) s' = Dir.map T '' coverSet P (T.symm s') := by
  ext h'
  simp only [mem_coverSet, covers_mapFamily, Set.mem_image]
  constructor
  · intro hc
    exact ⟨Dir.comap T h', hc, Dir.map_comap T h'⟩
  · rintro ⟨h, hc, rfl⟩
    rw [Dir.comap_map]
    exact hc

/-- Evenness is preserved by transport. -/
lemma IsEven.map {P : LineFamily W} (hE : IsEven P) :
    IsEven (mapFamily T P) := by
  intro s'
  rw [coverSet_mapFamily, Set.ncard_image_of_injective _ (Dir.map_injective T)]
  exact hE (T.symm s')

/-! ## Transport of planes -/

/-- Planes transport along linear isomorphisms. -/
lemma IsPlane.map (hP : IsPlane W) :
    IsPlane (W.map (T : Γ →ₗ[ZMod 2] Γ')) := by
  constructor
  · exact ⟨(Dir.map T hP.dir₀ : Γ'), (Dir.map T hP.dir₀).2⟩
  · intro h'
    refine ⟨Dir.map T (hP.other (Dir.comap T h')), fun e0 => ?_⟩
    apply hP.other_ne (Dir.comap T h')
    apply T.injective
    rw [Dir.map_coe] at e0
    rw [e0, Dir.comap_coe, T.apply_symm_apply]
  · intro h' a' b' hah hbh hab
    have key := hP.eq_add_of_ne (Dir.comap T h') (Dir.comap T a') (Dir.comap T b')
      (fun e => hah (T.symm.injective e)) (fun e => hbh (T.symm.injective e))
      (fun e => hab (T.symm.injective e))
    simp only [Dir.comap_coe] at key
    apply T.symm.injective
    rw [key, map_add]

/-- The transported companion direction avoids `h'`. -/
lemma Dir.map_other_ne (hP : IsPlane W)
    (h' : Dir (W.map (T : Γ →ₗ[ZMod 2] Γ'))) :
    (Dir.map T (hP.other (Dir.comap T h')) : Γ') ≠ (h' : Γ') := by
  intro e0
  apply hP.other_ne (Dir.comap T h')
  apply T.injective
  rw [Dir.map_coe] at e0
  rw [e0, Dir.comap_coe, T.apply_symm_apply]

/-! ## The naturality square -/

/-- **Corollary A2** (naturality): transport commutes with the classification,
`T_* (Φ_W(m)) = Φ_{T W}(T m)`. -/
theorem mapFamily_localFamily (hP : IsPlane W) (m : Γ) :
    mapFamily T (localFamily hP m) = localFamily (hP.map T) (T m) := by
  funext h'
  show lineEquivAt T (Dir.comap T h') h' _
      (lineMk (Dir.comap T h') m + hP.kappa (Dir.comap T h'))
    = lineMk h' (T m) + (hP.map T).kappa h'
  rw [map_add, lineEquivAt_lineMk, hP.kappa_def, lineEquivAt_lineMk,
    (hP.map T).kappa_eq h' (Dir.map T (hP.other (Dir.comap T h')))
      (Dir.map_other_ne T hP h'),
    Dir.map_coe]

/-- Naturality at the level of the classifying bijections:
`Φ_{T W} ∘ T = T_* ∘ Φ_W`. -/
theorem localEquiv_naturality (hP : IsPlane W) (m : Γ) :
    (localEquiv (hP.map T) (T m)).val
      = mapFamily T (localFamily hP m) :=
  (mapFamily_localFamily T hP m).symm

end AffineCDC
