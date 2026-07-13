import AffineCDC.LocalClassification

/-!
# Torsor packaging (Corollary A1)

`LocalEvenFamily W` is a `Γ`-torsor and `Φ_W` an affine isomorphism.

The torsor structure cannot be a global `instance`: it exists only when `W`
is a plane (`IsPlane W` is a `Prop` hypothesis), so it is packaged as a
definition `localTorsor hP`, together with the bundled affine equivalence
`localAffineEquiv hP : Γ ≃ᵃ[𝔽₂] LocalEvenFamily W`.

`localTorsor_vadd` identifies the abstract action with the geometric one:
`a +ᵥ P` is the translated family `translate a P`.
-/

namespace AffineCDC

variable {Γ : Type*} [AddCommGroup Γ] [Module (ZMod 2) Γ]
variable {W : Submodule (ZMod 2) Γ}

/-- The `Γ`-torsor structure on the local solution space (Corollary A1).
Not an instance: it requires the plane hypothesis. -/
@[reducible] noncomputable def localTorsor (hP : IsPlane W) :
    AddTorsor Γ (LocalEvenFamily W) where
  vadd a P := localEquiv hP (a + (localEquiv hP).symm P)
  zero_vadd P := by
    show localEquiv hP (0 + (localEquiv hP).symm P) = P
    rw [zero_add, Equiv.apply_symm_apply]
  add_vadd a b P := by
    show localEquiv hP ((a + b) + (localEquiv hP).symm P)
        = localEquiv hP (a + (localEquiv hP).symm
            (localEquiv hP (b + (localEquiv hP).symm P)))
    rw [Equiv.symm_apply_apply, add_assoc]
  vsub P Q := (localEquiv hP).symm P + (localEquiv hP).symm Q
  nonempty := ⟨localEquiv hP 0⟩
  vsub_vadd' P Q := by
    show localEquiv hP
        (((localEquiv hP).symm P + (localEquiv hP).symm Q)
          + (localEquiv hP).symm Q) = P
    rw [char2_add_cancel_right, Equiv.apply_symm_apply]
  vadd_vsub' a P := by
    show (localEquiv hP).symm (localEquiv hP (a + (localEquiv hP).symm P))
        + (localEquiv hP).symm P = a
    rw [Equiv.symm_apply_apply, char2_add_cancel_right]

/-- The abstract torsor action is the geometric translation of families. -/
lemma localTorsor_vadd (hP : IsPlane W) (a : Γ) (P : LocalEvenFamily W) :
    ((localTorsor hP).vadd a P : LocalEvenFamily W).val
      = translate a P.val := by
  show localFamily hP (a + (localEquiv hP).symm P) = _
  have hval : P.val = localFamily hP ((localEquiv hP).symm P) := by
    have := (localEquiv hP).apply_symm_apply P
    exact congrArg Subtype.val this.symm
  rw [hval, add_comm a, localFamily_translate]

/-- **Corollary A1**, bundled: the classification is an affine isomorphism
of `Γ`-torsors. -/
noncomputable def localAffineEquiv (hP : IsPlane W) :
    @AffineEquiv (ZMod 2) Γ (LocalEvenFamily W) Γ Γ _ _ _ _ _ _
      (localTorsor hP) :=
  letI := localTorsor hP
  { toEquiv := localEquiv hP
    linear := LinearEquiv.refl _ _
    map_vadd' := fun m a => by
      show localEquiv hP (a + m)
          = localEquiv hP (a + (localEquiv hP).symm (localEquiv hP m))
      rw [Equiv.symm_apply_apply] }

end AffineCDC
