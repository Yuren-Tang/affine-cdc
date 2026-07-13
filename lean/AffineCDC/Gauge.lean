import Mathlib

/-!
# Gauge classification (T4, abstract part)

For a fixed linear map `δ : C⁰ → C¹` over an arbitrary field, an *affine
gluing system* is the equation `δ m = c`; regauging the local origins
(`m ↦ m + a`) replaces `c` by `c + δ a`.

* `GaugeEquiv δ` is this equivalence of systems (C1);
* `gaugeEquiv_iff`: two systems are gauge-equivalent iff they have the same
  class in `coker δ` — so `[c]` is a *complete* invariant
  (`invariant_eq_of_gaugeEquiv` is the ready-to-use form);
* `exists_solution_iff`: the system is solvable iff `[c] = 0` (obstruction);
* `gaugeClassesEquiv`: the induced bijection
  `C¹/∼ ≃ coker δ`;
* `mem_range_iff_forall_dual` (C2): the dual criterion, valid in arbitrary
  dimension over a field.

Everything here is graph-free linear algebra; the specialization
`δ_f : Γ^V → ⊕ₑ Q_e`, `c_f` (C3) enters with the graph layer (T7 prep).
-/

namespace AffineCDC

variable {K : Type*} [Field K]
variable {C0 C1 : Type*} [AddCommGroup C0] [Module K C0]
  [AddCommGroup C1] [Module K C1]
variable (δ : C0 →ₗ[K] C1)

/-- Gauge equivalence of affine gluing systems with linear part `δ`:
`c'` arises from `c` by re-choosing local origins. -/
def GaugeEquiv (c c' : C1) : Prop := ∃ a : C0, c' = c + δ a

/-- The cokernel class of the right-hand side. -/
abbrev gaugeClass (c : C1) : C1 ⧸ LinearMap.range δ :=
  Submodule.Quotient.mk c

/-- **C1, completeness**: two systems are gauge-equivalent iff their
cokernel classes agree.  `[c]` is a complete invariant of the system under
local regauging. -/
theorem gaugeEquiv_iff {c c' : C1} :
    GaugeEquiv δ c c' ↔ gaugeClass δ c = gaugeClass δ c' := by
  rw [Submodule.Quotient.eq]
  constructor
  · rintro ⟨a, rfl⟩
    refine ⟨-a, ?_⟩
    rw [map_neg]
    abel
  · rintro ⟨a, ha⟩
    refine ⟨-a, ?_⟩
    rw [map_neg, ha]
    abel

/-- Any gauge-invariant quantity is a function of the cokernel class. -/
theorem invariant_eq_of_gaugeEquiv {X : Type*} (I : C1 → X)
    (hI : ∀ c c', GaugeEquiv δ c c' → I c = I c') {c c' : C1}
    (h : gaugeClass δ c = gaugeClass δ c') : I c = I c' :=
  hI c c' ((gaugeEquiv_iff δ).mpr h)

/-- `GaugeEquiv` is an equivalence relation. -/
def gaugeSetoid : Setoid C1 where
  r := GaugeEquiv δ
  iseqv := by
    constructor
    · intro c
      exact ⟨0, by simp⟩
    · intro a b h
      rw [gaugeEquiv_iff] at *
      exact h.symm
    · intro a b c h1 h2
      rw [gaugeEquiv_iff] at *
      exact h1.trans h2

/-- **C1, classification**: gauge classes of systems are exactly the points
of `coker δ`. -/
noncomputable def gaugeClassesEquiv :
    Quotient (gaugeSetoid δ) ≃ (C1 ⧸ LinearMap.range δ) :=
  Equiv.ofBijective
    (Quotient.lift (gaugeClass δ) fun _ _ h => (gaugeEquiv_iff δ).mp h)
    ⟨by
      rintro ⟨c⟩ ⟨c'⟩ h
      exact Quotient.sound ((gaugeEquiv_iff δ).mpr h),
     fun q => by
      obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ q
      exact ⟨⟦c⟧, rfl⟩⟩

/-- **C1, obstruction**: the system `δ m = c` is solvable iff `[c] = 0`. -/
theorem exists_solution_iff (c : C1) :
    (∃ m : C0, δ m = c) ↔ gaugeClass δ c = 0 := by
  rw [Submodule.Quotient.mk_eq_zero]
  exact ⟨fun ⟨m, hm⟩ => ⟨m, hm⟩, fun ⟨m, hm⟩ => ⟨m, hm⟩⟩

/-- **C2, dual criterion** (arbitrary dimension, over a field): `c` lies in
the range of `δ` iff every functional annihilating the range annihilates
`c`. -/
theorem mem_range_iff_forall_dual (c : C1) :
    c ∈ LinearMap.range δ ↔
      ∀ η : Module.Dual K C1, (∀ x, η (δ x) = 0) → η c = 0 := by
  constructor
  · rintro ⟨m, rfl⟩ η hη
    exact hη m
  · intro h
    by_contra hc
    obtain ⟨f, hf, hmap⟩ :=
      Submodule.exists_dual_map_eq_bot_of_notMem hc inferInstance
    apply hf
    apply h
    intro x
    have hx : f (δ x) ∈ (LinearMap.range δ).map f :=
      Submodule.mem_map_of_mem ⟨x, rfl⟩
    rw [hmap] at hx
    exact (Submodule.mem_bot K).mp hx

/-- Solvability in dual form: the combination of C1 and C2 used by the
original manuscript's Lemma 2.2. -/
theorem exists_solution_iff_forall_dual (c : C1) :
    (∃ m : C0, δ m = c) ↔
      ∀ η : Module.Dual K C1, (∀ x, η (δ x) = 0) → η c = 0 := by
  rw [← mem_range_iff_forall_dual]
  exact ⟨fun ⟨m, hm⟩ => ⟨m, hm⟩, fun ⟨m, hm⟩ => ⟨m, hm⟩⟩

end AffineCDC
