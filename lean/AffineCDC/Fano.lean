import AffineCDC.Dart
import AffineCDC.Rank

/-!
# The Fano compatibility theorem (T7, F2)

The endpoint of the library: for a cubic dart structure with a nowhere-zero
flow whose vertex planes have codimension one (`dim Γ = 3`), the gluing
system is solvable —

`∃ m : V → Γ, δ_f m = c_f`, i.e. `[c_f] = 0 ∈ coker δ_f`

(`DartFlow.exists_gluing`; `exists_gluing_of_finrank_three` takes the
hypothesis in the form `finrank Γ = 3`).  Combined with the local
classification (T1) this produces the glued global even families behind the
cycle double cover; the extraction of the cover itself (the original
Lemma 2.1) is outside the library's endpoint by the project's comparison
decision.

Proof skeleton (the original Lemma 2.2, in the purified language):
by the dual criterion (T4 C2) it suffices that every functional `η`
annihilating `im δ_f` annihilates `c_f`.  The components of such an `η`
assemble, at each vertex, into a legal dual configuration (T5); the value
`η(c_f)` is the sum over darts of cross-pairing values, which per vertex is
the bit `β` (T5 D1); the branching identity (F1, the codimension-one input)
converts each `β` into a support count, and every edge is counted twice —
zero in characteristic two.
-/

namespace AffineCDC

open Module

variable {Δ V Γ : Type*} [AddCommGroup Γ] [Module (ZMod 2) Γ]

/-! ## Triple summation utilities (graph-free) -/

section Triple

variable {W : Submodule (ZMod 2) Γ}

private lemma triple_distinct {x y z : Dir W}
    (hs : (x : Γ) + (y : Γ) + (z : Γ) = 0) :
    (y : Γ) ≠ (x : Γ) ∧ x ≠ y ∧ x ≠ z ∧ y ≠ z := by
  have hyx : (y : Γ) ≠ (x : Γ) := by
    intro e
    apply z.coe_ne_zero
    rw [e, char2_add_self, zero_add] at hs
    exact hs
  have hzx : (z : Γ) ≠ (x : Γ) := by
    intro e
    apply y.coe_ne_zero
    rw [e, add_comm (x : Γ) (y : Γ), add_assoc, char2_add_self, add_zero] at hs
    exact hs
  have hzy : (z : Γ) ≠ (y : Γ) := by
    intro e
    apply x.coe_ne_zero
    rw [e, add_assoc, char2_add_self, add_zero] at hs
    exact hs
  exact ⟨hyx, fun e => hyx (congrArg Subtype.val e).symm,
    fun e => hzx (congrArg Subtype.val e).symm,
    fun e => hzy (congrArg Subtype.val e).symm⟩

private lemma triple_complete (hP : IsPlane W) {x y z : Dir W}
    (hs : (x : Γ) + (y : Γ) + (z : Γ) = 0) (h : Dir W) :
    h = x ∨ h = y ∨ h = z := by
  obtain ⟨hyx, -, -, -⟩ := triple_distinct hs
  rcases hP.trichotomy x y hyx h with h1 | h1 | h1
  · exact Or.inl h1
  · exact Or.inr (Or.inl h1)
  · exact Or.inr (Or.inr (Subtype.ext (h1.trans (char2_add_eq_zero_iff.mp hs))))

private lemma sum_dir_eq [Fintype (Dir W)] {M : Type*} [AddCommMonoid M]
    (hP : IsPlane W) (g : Dir W → M) {x y z : Dir W}
    (hs : (x : Γ) + (y : Γ) + (z : Γ) = 0) :
    ∑ h : Dir W, g h = g x + g y + g z := by
  classical
  obtain ⟨-, hxy, hxz, hyz⟩ := triple_distinct hs
  have huniv : (Finset.univ : Finset (Dir W)) = {x, y, z} := by
    ext h
    simp only [Finset.mem_univ, true_iff, Finset.mem_insert,
      Finset.mem_singleton]
    exact triple_complete hP hs h
  rw [huniv, Finset.sum_insert (by simp [hxy, hxz]),
    Finset.sum_insert (by simp [hyz]), Finset.sum_singleton, ← add_assoc]

/-- A sum-zero triple of directions in any plane. -/
private lemma exists_triple (hP : IsPlane W) :
    ∃ x y z : Dir W, (x : Γ) + (y : Γ) + (z : Γ) = 0 := by
  refine ⟨hP.dir₀, hP.other hP.dir₀,
    Dir.add hP.dir₀ (hP.other hP.dir₀) (hP.other_ne hP.dir₀), ?_⟩
  rw [Dir.add_coe, add_assoc, char2_add_left_eq, char2_add_self]

end Triple

namespace DartFlow

variable (D : DartFlow Δ V Γ)

section Global

variable [Fintype Δ] [DecidableEq Δ] [Fintype V] [DecidableEq V]

/-- **F2** (Fano compatibility theorem): if every vertex plane has
codimension one, the gluing system `δ_f m = c_f` is solvable — the natural
compatibility class vanishes. -/
theorem exists_gluing
    (hcodim : ∀ u : V, finrank (ZMod 2) (Γ ⧸ D.W u) = 1) :
    ∃ m : V → Γ, D.delta m = D.cfam := by
  rw [exists_solution_iff_forall_dual]
  intro η hη
  -- decomposition of `η` along darts
  have hdecomp : ∀ x : (d : Δ) → LineSpace (D.dir d),
      η x = ∑ d, η (Pi.single d (x d)) := by
    intro x
    conv_lhs => rw [← Finset.univ_sum_single x]
    rw [map_sum]
  -- the vertex condition: the edge functionals sum to zero at each vertex
  have hvert : ∀ u : V,
      ∑ d ∈ Finset.univ.filter (fun d => D.vtx d = u), D.psi η d = 0 := by
    intro u
    apply LinearMap.ext
    intro γ
    have h0 := hη (Pi.single u γ)
    rw [hdecomp] at h0
    have hterm : ∀ d : Δ, η (Pi.single d (D.delta (Pi.single u γ) d))
        = (if D.vtx d = u then D.theta η d γ else 0)
          + (if D.vtx (D.σ d) = u then D.theta η d γ else 0) := by
      intro d
      rw [D.delta_apply, Pi.single_apply, Pi.single_apply, ← D.theta_apply,
        map_add, apply_ite (D.theta η d), apply_ite (D.theta η d), map_zero]
    rw [Finset.sum_congr rfl (fun d _ => hterm d),
      Finset.sum_add_distrib] at h0
    have hre : ∑ d, (if D.vtx (D.σ d) = u then D.theta η d γ else 0)
        = ∑ d, (if D.vtx d = u then D.theta η (D.σ d) γ else 0) := by
      rw [← Equiv.sum_comp (Function.Involutive.toPerm D.σ D.invol)
        (fun d => if D.vtx d = u then D.theta η (D.σ d) γ else 0)]
      apply Finset.sum_congr rfl
      intro d _
      show (if D.vtx (D.σ d) = u then D.theta η d γ else 0) = _
      rw [show (Function.Involutive.toPerm D.σ D.invol) d = D.σ d from rfl,
        D.invol d]
    rw [hre, ← Finset.sum_add_distrib] at h0
    have hcomb : ∀ d : Δ,
        ((if D.vtx d = u then D.theta η d γ else 0)
          + (if D.vtx d = u then D.theta η (D.σ d) γ else 0))
        = (if D.vtx d = u then D.psi η d γ else 0) := by
      intro d
      by_cases hd : D.vtx d = u
      · simp only [hd, if_true]
        rfl
      · simp only [hd, if_false, add_zero]
    rw [Finset.sum_congr rfl (fun d _ => hcomb d), ← Finset.sum_filter] at h0
    rw [LinearMap.coe_sum, Finset.sum_apply, LinearMap.zero_apply]
    exact h0
  -- the vertex configurations and their bits
  have hmem : ∀ u : V, D.vertexConfig η u ∈ dualConfig (D.W u) := by
    intro u
    letI : Fintype (Dir (D.W u)) := Fintype.ofEquiv _ (D.dartEquiv u)
    have hcfg_sum : ∑ h : Dir (D.W u), D.vertexConfig η u h = 0 := by
      have h1 := hvert u
      rw [Finset.sum_subtype (p := fun d => D.vtx d = u) _ (by simp)
        (fun d => D.psi η d)] at h1
      have h2 : ∑ h : Dir (D.W u), D.vertexConfig η u h
          = ∑ s : {d : Δ // D.vtx d = u}, D.psi η s.1 :=
        Equiv.sum_comp (D.dartEquiv u).symm (fun s => D.psi η s.1)
      rw [h2]
      exact h1
    refine ⟨fun h => D.vertexConfig_eval_self η u h, fun a b c habc => ?_⟩
    rw [← sum_dir_eq (D.plane u) (D.vertexConfig η u) habc]
    exact hcfg_sum
  -- per-vertex: cross values sum to bits sum
  have hvcount : ∀ u : V,
      ∑ d ∈ Finset.univ.filter (fun d => D.vtx d = u),
        (D.psi η d) (D.f (D.next d))
      = ∑ d ∈ Finset.univ.filter (fun d => D.vtx d = u),
          nzBit (D.psi η d) := by
    intro u
    letI : Fintype (Dir (D.W u)) := Fintype.ofEquiv _ (D.dartEquiv u)
    obtain ⟨x, y, z, hs⟩ := exists_triple (D.plane u)
    -- each cross value is the bit β of the vertex configuration
    have hterm1 : ∀ h : Dir (D.W u),
        (D.psi η ((D.dartEquiv u).symm h).1)
          (D.f (D.next ((D.dartEquiv u).symm h).1))
        = crossBit (D.plane u) ⟨D.vertexConfig η u, hmem u⟩ := by
      intro h
      have hmem' : D.f (D.next ((D.dartEquiv u).symm h).1) ∈ D.W u := by
        have hh := D.next_mem ((D.dartEquiv u).symm h).1
        rwa [((D.dartEquiv u).symm h).2] at hh
      have hane : (D.f (D.next ((D.dartEquiv u).symm h).1)) ≠ (h : Γ) := by
        rw [← D.f_dartEquiv_symm u h]
        exact D.next_ne ((D.dartEquiv u).symm h).1
      exact crossBit_eq (D.plane u) ⟨D.vertexConfig η u, hmem u⟩
        (h' := ⟨D.f (D.next ((D.dartEquiv u).symm h).1), hmem',
          D.nz (D.next ((D.dartEquiv u).symm h).1)⟩) hane
    -- convert both filter sums to sums over directions
    rw [Finset.sum_subtype (p := fun d => D.vtx d = u) _ (by simp)
        (fun d => (D.psi η d) (D.f (D.next d))),
      Finset.sum_subtype (p := fun d => D.vtx d = u) _ (by simp)
        (fun d => nzBit (D.psi η d)),
      ← Equiv.sum_comp (D.dartEquiv u).symm
        (fun s => (D.psi η s.1) (D.f (D.next s.1))),
      ← Equiv.sum_comp (D.dartEquiv u).symm (fun s => nzBit (D.psi η s.1))]
    rw [Finset.sum_congr rfl (fun h _ => hterm1 h)]
    rw [sum_dir_eq (D.plane u)
      (fun _ => crossBit (D.plane u) ⟨D.vertexConfig η u, hmem u⟩) hs]
    rw [sum_dir_eq (D.plane u)
      (fun h => nzBit (D.psi η ((D.dartEquiv u).symm h).1)) hs]
    rw [char2_add_self, zero_add]
    exact crossBit_eq_parity (D.plane u) (hcodim u)
      ⟨D.vertexConfig η u, hmem u⟩ hs
  -- assemble: η (c_f) = ∑ over darts of cross values
  have hcfam : η D.cfam = ∑ d, (D.psi η d) (D.f (D.next d)) := by
    rw [hdecomp D.cfam]
    have hterm : ∀ d : Δ, η (Pi.single d (D.cfam d))
        = D.theta η d (D.f (D.next d))
          + D.theta η d (D.f (D.next (D.σ d))) := by
      intro d
      rw [show D.cfam d
          = lineMk (D.dir d) (D.f (D.next d) + D.f (D.next (D.σ d))) from rfl,
        map_add, Pi.single_add, map_add, ← D.theta_apply, ← D.theta_apply]
    rw [Finset.sum_congr rfl (fun d _ => hterm d), Finset.sum_add_distrib]
    have hre2 : ∑ d, D.theta η d (D.f (D.next (D.σ d)))
        = ∑ d, D.theta η (D.σ d) (D.f (D.next d)) := by
      rw [← Equiv.sum_comp (Function.Involutive.toPerm D.σ D.invol)
        (fun d => D.theta η (D.σ d) (D.f (D.next d)))]
      apply Finset.sum_congr rfl
      intro d _
      show D.theta η d (D.f (D.next (D.σ d))) = _
      rw [show (Function.Involutive.toPerm D.σ D.invol) d = D.σ d from rfl,
        D.invol d]
    rw [hre2, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro d _
    rfl
  rw [hcfam,
    ← Finset.sum_fiberwise_of_maps_to (fun d _ => Finset.mem_univ (D.vtx d))
      (fun d => (D.psi η d) (D.f (D.next d))),
    Finset.sum_congr rfl (fun u _ => hvcount u),
    Finset.sum_fiberwise_of_maps_to (fun d _ => Finset.mem_univ (D.vtx d))
      (fun d => nzBit (D.psi η d))]
  -- every edge is counted twice: the involution pairing
  apply Finset.sum_ninvolution D.σ
  · intro d
    rw [D.psi_σ η d]
    exact char2_add_self _
  · intro d _
    exact D.no_fix d
  · intro d
    exact Finset.mem_univ _
  · intro d
    exact D.invol d

/-- **F2** with the classical hypothesis `dim Γ = 3`. -/
theorem exists_gluing_of_finrank_three (h3 : finrank (ZMod 2) Γ = 3) :
    ∃ m : V → Γ, D.delta m = D.cfam := by
  haveI : FiniteDimensional (ZMod 2) Γ :=
    Module.finite_of_finrank_pos (by omega)
  apply D.exists_gluing
  intro u
  have h2 := (D.plane u).finrank_eq_two
  have hq := Submodule.finrank_quotient_add_finrank (D.W u)
  omega

/-- **F3** (label form): a global gauge `m` making all local labels agree
along every edge — the label of `Φ_{W_u}(m_u)` at a dart equals the line of
the opposite endpoint's family, read in the same edge quotient.  By B1
(lines = cosets) this is precisely the gluing of the local even families. -/
theorem exists_gluing_labels
    (hcodim : ∀ u : V, finrank (ZMod 2) (Γ ⧸ D.W u) = 1) :
    ∃ m : V → Γ, ∀ d : Δ,
      localFamily (D.plane (D.vtx d)) (m (D.vtx d)) (D.dir d)
        = lineMk (D.dir d) (m (D.vtx (D.σ d)) + D.f (D.next (D.σ d))) := by
  obtain ⟨m, hm⟩ := D.exists_gluing hcodim
  refine ⟨m, fun d => ?_⟩
  have hd := congrFun hm d
  rw [D.delta_apply, D.cfam_eq_kappa, map_add] at hd
  rw [show localFamily (D.plane (D.vtx d)) (m (D.vtx d)) (D.dir d)
      = lineMk (D.dir d) (m (D.vtx d))
        + (D.plane (D.vtx d)).kappa (D.dir d) from rfl,
    map_add]
  have h2 := congrArg
    (fun q => lineMk (D.dir d) (m (D.vtx d)) + q) hd
  rw [char2_add_left_eq] at h2
  rw [h2, add_assoc, char2_add_cancel_right]

end Global

end DartFlow

end AffineCDC
