import AffineCDC.Dart
import AffineCDC.Fano
import AffineCDC.OppositeFiber

/-!
# The double cover (G, part 1: supports)

From a glued gauge `m` (F3) we extract, for each `s : Γ`, the *support*
`Msupp m s` — the darts whose assigned line passes through `s`.  This file
establishes the three structural facts about supports:

* `mem_Msupp_iff_master`: membership is the master computation of T1 —
  `d ∈ Msupp m s ↔ s + m_u ∈ W_u ∖ {0, f d}` (definitionally
  `covers_localFamily_iff`);
* `Msupp_sigma` (**G0**): supports are `σ`-closed — the point sets of the
  two endpoint lines coincide, because gluing makes them the *same coset
  with the same representative*;
* `setOf_mem_Msupp` (**G3**): each dart lies in the supports of exactly the
  two points of its line — every edge is covered exactly twice (B1).

Part 2 (`Cycle.lean`, planned): the vertex condition 0-or-2 (**G1**), the
rotation `ρ = partner ∘ σ` whose orbits are the cycles (**G2**), and the
packaged cycle double cover (**G4**).
-/

namespace AffineCDC

namespace DartFlow

variable {Δ V Γ : Type*} [AddCommGroup Γ] [Module (ZMod 2) Γ]
variable (D : DartFlow Δ V Γ)

/-- The line assigned to a dart by the gauge `m`. -/
noncomputable def famAt (m : V → Γ) (d : Δ) : LineSpace (D.dir d) :=
  localFamily (D.plane (D.vtx d)) (m (D.vtx d)) (D.dir d)

/-- The assigned line through the canonical representative
`m_u + f(next d)`. -/
lemma famAt_eq (m : V → Γ) (d : Δ) :
    D.famAt m d = lineMk (D.dir d) (m (D.vtx d) + D.f (D.next d)) := by
  show lineMk (D.dir d) (m (D.vtx d))
      + (D.plane (D.vtx d)).kappa (D.dir d) = _
  rw [(D.plane (D.vtx d)).kappa_eq (D.dir d)
    ⟨D.f (D.next d), D.next_mem d, D.nz (D.next d)⟩ (D.next_ne d), ← map_add]

/-- A gauge is *glued* when every assigned line agrees with the one seen
from the opposite endpoint (the conclusion of F3). -/
def Glued (m : V → Γ) : Prop :=
  ∀ d : Δ, D.famAt m d
    = lineMk (D.dir d) (m (D.vtx (D.σ d)) + D.f (D.next (D.σ d)))

/-- F3, restated: glued gauges exist (codimension-one hypothesis). -/
theorem exists_glued [Fintype Δ] [DecidableEq Δ] [Fintype V] [DecidableEq V]
    (hcodim : ∀ u : V, Module.finrank (ZMod 2) (Γ ⧸ D.W u) = 1) :
    ∃ m : V → Γ, D.Glued m :=
  D.exists_gluing_labels hcodim

/-- The support of a point `s`: darts whose assigned line passes
through `s`. -/
def Msupp (m : V → Γ) (s : Γ) : Set Δ :=
  {d | lineMk (D.dir d) s = D.famAt m d}

/-- Membership in the support is the master computation of T1. -/
lemma mem_Msupp_iff_master (m : V → Γ) (s : Γ) (d : Δ) :
    d ∈ D.Msupp m s ↔
      s + m (D.vtx d) ∈ D.W (D.vtx d) ∧ s + m (D.vtx d) ≠ 0
        ∧ s + m (D.vtx d) ≠ D.f d :=
  covers_localFamily_iff

/-- Membership through the canonical representative. -/
lemma mem_Msupp_iff_rep (m : V → Γ) (s : Γ) (d : Δ) :
    d ∈ D.Msupp m s ↔
      s + (m (D.vtx d) + D.f (D.next d)) = 0
        ∨ s + (m (D.vtx d) + D.f (D.next d)) = D.f d := by
  show lineMk (D.dir d) s = D.famAt m d ↔ _
  rw [D.famAt_eq, lineMk_eq_iff, D.dir_coe]

/-- Membership seen from the opposite endpoint, for a glued gauge. -/
lemma mem_Msupp_iff_glued {m : V → Γ} (hm : D.Glued m) (s : Γ) (d : Δ) :
    d ∈ D.Msupp m s ↔
      s + (m (D.vtx (D.σ d)) + D.f (D.next (D.σ d))) = 0
        ∨ s + (m (D.vtx (D.σ d)) + D.f (D.next (D.σ d))) = D.f d := by
  show lineMk (D.dir d) s = D.famAt m d ↔ _
  rw [hm d, lineMk_eq_iff, D.dir_coe]

/-- **G0**: supports of a glued gauge are `σ`-closed — the two endpoints
assign the same set of points to an edge. -/
theorem Msupp_sigma {m : V → Γ} (hm : D.Glued m) (s : Γ) (d : Δ) :
    D.σ d ∈ D.Msupp m s ↔ d ∈ D.Msupp m s := by
  rw [D.mem_Msupp_iff_rep m s (D.σ d), D.mem_Msupp_iff_glued hm s d, D.f_σ d]

/-- **G3**: a dart lies in exactly the supports of the two points of its
line — every edge is covered exactly twice. -/
theorem setOf_mem_Msupp (m : V → Γ) (d : Δ) :
    {s : Γ | d ∈ D.Msupp m s}
      = {m (D.vtx d) + D.f (D.next d),
         m (D.vtx d) + D.f (D.next d) + D.f d} := by
  have h2 : {s : Γ | lineMk (D.dir d) s
        = lineMk (D.dir d) (m (D.vtx d) + D.f (D.next d))}
      = {m (D.vtx d) + D.f (D.next d),
         m (D.vtx d) + D.f (D.next d) + D.f d} :=
    coset_eq_pair (D.dir d) (m (D.vtx d) + D.f (D.next d))
  rw [← h2]
  ext s
  show (lineMk (D.dir d) s = D.famAt m d)
    ↔ (lineMk (D.dir d) s
        = lineMk (D.dir d) (m (D.vtx d) + D.f (D.next d)))
  rw [D.famAt_eq]

/-- **G3**, counted: the set of points covering a given dart has exactly
two elements. -/
theorem ncard_setOf_mem_Msupp (m : V → Γ) (d : Δ) :
    {s : Γ | d ∈ D.Msupp m s}.ncard = 2 := by
  rw [D.setOf_mem_Msupp m d]
  refine Set.ncard_pair fun e => ?_
  exact D.nz d (add_left_cancel (a := m (D.vtx d) + D.f (D.next d))
    (b := (0 : Γ)) (by rw [add_zero]; exact e)).symm

end DartFlow

end AffineCDC
