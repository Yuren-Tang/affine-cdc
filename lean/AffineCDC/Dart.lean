import AffineCDC.Branching
import AffineCDC.Gauge
import AffineCDC.EdgeQuotient

/-!
# The dart layer (T7, F0)

A cubic graph with a nowhere-zero flow, in gauge-free combinatorial form:
darts (half-edges) with a fixed-point-free involution `σ` (edge pairing) and
a vertex map, each vertex seeing exactly the three directions of a plane.
No endpoint numbering, no vertex slots — the coordinates `endAt e 0/1` and
`edgeAt v i` of the original formalization do not exist here.

* `DartFlow`: the structure.  The field `cubic` — the value map from the
  dart fiber to `Dir (W u)` is a bijection — is the distilled form of
  "cubic + conservation + nowhere-zero" (see the paper spec T7 F0);
* `next d`: a chosen companion dart at the same vertex (choice quarantined;
  all classes built from it are choice-free by `kappa_eq`);
* `delta`, `cfam`: the gluing system `δ_f m = c_f` over darts.  Working
  dart-wise dissolves the `Q_{σd} = Q_d` transport: the `d`-component and
  the `σd`-component of the system are (logically equivalent) statements in
  the two quotients, and we simply require all of them;
* `cfam_eq_kappa` (C3, canonical form): the right-hand side is
  `κ_d + [κ_{σd}]` — the natural compatibility class;
* `theta`, `psi`, `vertexConfig`: the components of a dual functional and
  the induced configuration at each vertex (used by F2).
-/

namespace AffineCDC

open Module

variable {Δ V Γ : Type*} [AddCommGroup Γ] [Module (ZMod 2) Γ]

/-- A cubic dart structure carrying a nowhere-zero conservative flow:
darts, edge involution, vertex map, flow values, and the vertex planes. -/
structure DartFlow (Δ V : Type*) (Γ : Type*)
    [AddCommGroup Γ] [Module (ZMod 2) Γ] where
  /-- The edge-pairing involution. -/
  σ : Δ → Δ
  invol : ∀ d, σ (σ d) = d
  /-- Looplessness: no dart is its own partner. -/
  no_fix : ∀ d, σ d ≠ d
  /-- The vertex of a dart. -/
  vtx : Δ → V
  /-- The flow value of a dart. -/
  f : Δ → Γ
  /-- The flow is undirected (characteristic two). -/
  f_σ : ∀ d, f (σ d) = f d
  /-- The vertex planes. -/
  W : V → Submodule (ZMod 2) Γ
  plane : ∀ u, IsPlane (W u)
  mem : ∀ d, f d ∈ W (vtx d)
  nz : ∀ d, f d ≠ 0
  /-- Cubic + conservation + nowhere-zero, distilled: at each vertex the
  value map from the dart fiber to the directions of the plane is a
  bijection. -/
  cubic : ∀ u : V, Function.Bijective
    (fun d : {d : Δ // vtx d = u} =>
      (⟨f d.1, (congrArg W d.2) ▸ mem d.1, nz d.1⟩ : Dir (W u)))

namespace DartFlow

variable (D : DartFlow Δ V Γ)

/-- The direction of a dart in its vertex plane. -/
def dir (d : Δ) : Dir (D.W (D.vtx d)) := ⟨D.f d, D.mem d, D.nz d⟩

@[simp] lemma dir_coe (d : Δ) : (D.dir d : Γ) = D.f d := rfl

/-- The vertex bijection between darts at `u` and directions of `W u`. -/
noncomputable def dartEquiv (u : V) :
    {d : Δ // D.vtx d = u} ≃ Dir (D.W u) :=
  Equiv.ofBijective _ (D.cubic u)

lemma f_dartEquiv_symm (u : V) (h : Dir (D.W u)) :
    D.f ((D.dartEquiv u).symm h).1 = (h : Γ) := by
  have h1 := (D.dartEquiv u).apply_symm_apply h
  have h2 := congrArg (fun x : Dir (D.W u) => (x : Γ)) h1
  exact h2

/-! ## The companion dart -/

lemma exists_companion (d : Δ) :
    ∃ d', D.vtx d' = D.vtx d ∧ D.f d' ≠ D.f d := by
  obtain ⟨dd, hdd⟩ :=
    (D.cubic (D.vtx d)).2 ((D.plane (D.vtx d)).other (D.dir d))
  refine ⟨dd.1, dd.2, ?_⟩
  have hval := congrArg (fun x : Dir (D.W (D.vtx d)) => (x : Γ)) hdd
  simp only at hval
  rw [hval]
  exact (D.plane (D.vtx d)).other_ne (D.dir d)

/-- A chosen companion dart at the same vertex (choice quarantined). -/
noncomputable def next (d : Δ) : Δ := (D.exists_companion d).choose

lemma next_vtx (d : Δ) : D.vtx (D.next d) = D.vtx d :=
  (D.exists_companion d).choose_spec.1

lemma next_ne (d : Δ) : D.f (D.next d) ≠ D.f d :=
  (D.exists_companion d).choose_spec.2

lemma next_mem (d : Δ) : D.f (D.next d) ∈ D.W (D.vtx d) := by
  have h := D.mem (D.next d)
  rwa [D.next_vtx d] at h

/-! ## The gluing system -/

/-- The linear part of the gluing system: `m ↦ ([m_u + m_{u'}])_d`. -/
noncomputable def delta :
    (V → Γ) →ₗ[ZMod 2] ((d : Δ) → LineSpace (D.dir d)) where
  toFun m := fun d => lineMk (D.dir d) (m (D.vtx d) + m (D.vtx (D.σ d)))
  map_add' m m' := by
    funext d
    show lineMk (D.dir d) _
      = lineMk (D.dir d) _ + lineMk (D.dir d) _
    rw [← map_add]
    congr 1
    simp only [Pi.add_apply]
    abel
  map_smul' c m := by
    funext d
    show lineMk (D.dir d) _ = c • lineMk (D.dir d) _
    rw [← map_smul]
    congr 1
    simp only [Pi.smul_apply, smul_add]

@[simp] lemma delta_apply (m : V → Γ) (d : Δ) :
    D.delta m d = lineMk (D.dir d) (m (D.vtx d) + m (D.vtx (D.σ d))) := rfl

/-- The compatibility family: at each dart, the sum of the residual classes
of the two endpoints. -/
noncomputable def cfam : (d : Δ) → LineSpace (D.dir d) :=
  fun d => lineMk (D.dir d) (D.f (D.next d) + D.f (D.next (D.σ d)))

/-- **C3, canonical form**: the compatibility family is
`κ_d + [κ_{σd}]` — the value is independent of the companion choice. -/
lemma cfam_eq_kappa (d : Δ) :
    D.cfam d = (D.plane (D.vtx d)).kappa (D.dir d)
      + lineMk (D.dir d) (D.f (D.next (D.σ d))) := by
  show lineMk (D.dir d) _ = _
  rw [map_add]
  congr 1
  exact ((D.plane (D.vtx d)).kappa_eq (D.dir d)
    ⟨D.f (D.next d), D.next_mem d, D.nz (D.next d)⟩ (D.next_ne d)).symm

/-! ## Components of a dual functional -/

section Dual

variable [DecidableEq Δ]
variable (η : Module.Dual (ZMod 2) ((d : Δ) → LineSpace (D.dir d)))

/-- The `d`-component of a dual functional, as a functional on `Γ`. -/
noncomputable def theta (d : Δ) : Module.Dual (ZMod 2) Γ :=
  η.comp ((LinearMap.single (ZMod 2) (fun d => LineSpace (D.dir d)) d).comp
    (lineMk (D.dir d)))

lemma theta_apply (d : Δ) (γ : Γ) :
    D.theta η d γ = η (Pi.single d (lineMk (D.dir d) γ)) := rfl

lemma theta_f (d : Δ) : D.theta η d (D.f d) = 0 := by
  rw [theta_apply,
    show lineMk (D.dir d) (D.f d) = 0 from lineMk_self (D.dir d)]
  simp

/-- The edge functional seen from a dart: `θ_d + θ_{σd}`.
Automatically `σ`-invariant. -/
noncomputable def psi (d : Δ) : Module.Dual (ZMod 2) Γ :=
  D.theta η d + D.theta η (D.σ d)

lemma psi_σ (d : Δ) : D.psi η (D.σ d) = D.psi η d := by
  unfold psi
  rw [D.invol d, add_comm]

lemma psi_f (d : Δ) : D.psi η d (D.f d) = 0 := by
  unfold psi
  simp only [LinearMap.add_apply]
  rw [D.theta_f η d, zero_add, ← D.f_σ d]
  exact D.theta_f η (D.σ d)

/-- The configuration induced at a vertex. -/
noncomputable def vertexConfig (u : V) :
    Dir (D.W u) → Module.Dual (ZMod 2) Γ :=
  fun h => D.psi η ((D.dartEquiv u).symm h).1

lemma vertexConfig_eval_self (u : V) (h : Dir (D.W u)) :
    D.vertexConfig η u h (h : Γ) = 0 := by
  show D.psi η _ (h : Γ) = 0
  rw [← D.f_dartEquiv_symm u h]
  exact D.psi_f η _

end Dual

end DartFlow

end AffineCDC
