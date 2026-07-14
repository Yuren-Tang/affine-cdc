import AffineCDC.Statement

/-!
# Circuit decomposition of even edge-sets

Self-contained graph theory over the definitions of `Statement.lean` (only
Mathlib + those definitions).  The classical fact:

> every finite even edge-set is an edge-disjoint union of cycles.

`exists_cycle_decomposition`: a finite even `F ⊆ E(G)` admits a multiset of
cycles covering every edge of `F` exactly once (and every non-edge zero
times).  This is what turns the even 2-regular subgraphs produced by the
affine construction into a genuine cover **by cycles** (minimal even sets),
matching the classical statement of the conjecture.

The proof is Veblen's argument: a nonempty even set is either already minimal
(a single cycle) or splits into two smaller even sets, by strong induction on
the number of edges.
-/

namespace AffineCDC.Statement

open Graph
open scoped Classical

variable {α β : Type*}

/-- Removing an even subset from an even set leaves an even set:
degrees subtract, and even minus even is even. -/
lemma IsEven.sdiff [Finite β] {G : Graph α β} {F D : Set β}
    (hDF : D ⊆ F) (hF : IsEven G F) (hD : IsEven G D) : IsEven G (F \ D) := by
  intro x
  have hIsub : D ∩ G.incidenceSet x ⊆ F ∩ G.incidenceSet x :=
    fun e he => ⟨hDF he.1, he.2⟩
  have hset : (F \ D) ∩ G.incidenceSet x
      = (F ∩ G.incidenceSet x) \ (D ∩ G.incidenceSet x) := by
    ext e; constructor
    · rintro ⟨⟨hF, hD⟩, hI⟩; exact ⟨⟨hF, hI⟩, fun h => hD h.1⟩
    · rintro ⟨⟨hF, hI⟩, hD⟩; exact ⟨⟨hF, fun h => hD ⟨h, hI⟩⟩, hI⟩
  rw [hset, Set.ncard_sdiff hIsub]
  exact (Nat.even_sub (Set.ncard_le_ncard hIsub (Set.toFinite _))).mpr
    (iff_of_true (hF x) (hD x))

/-- **Circuit decomposition.**  A finite even edge-set is covered exactly once
by a multiset of cycles. -/
theorem exists_cycle_decomposition [Finite β] (G : Graph α β) :
    ∀ (n : ℕ) (F : Set β), F.ncard = n → F ⊆ E(G) → IsEven G F →
      ∃ 𝒟 : Multiset (Set β), (∀ C ∈ 𝒟, IsCycle G C) ∧
        ∀ e, (𝒟.filter fun C => e ∈ C).card = if e ∈ F then 1 else 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro F hcard hFE hFeven
    rcases Set.eq_empty_or_nonempty F with hFempty | hFne
    · -- empty: the empty decomposition
      refine ⟨0, by simp, fun e => ?_⟩
      simp [hFempty]
    · by_cases hmin : ∀ D : Set β, D.Nonempty → D ⊆ F → IsEven G D → D = F
      · -- `F` is a cycle
        refine ⟨{F}, ?_, fun e => ?_⟩
        · intro C hC
          rw [Multiset.mem_singleton] at hC
          subst hC
          exact ⟨hFne, hFE, hFeven, hmin⟩
        · by_cases he : e ∈ F <;>
            simp [Multiset.filter_singleton, he]
      · -- split off a proper nonempty even subset
        push_neg at hmin
        obtain ⟨D, hDne, hDF, hDeven, hDproper⟩ := hmin
        have hDss : D ⊂ F := hDF.ssubset_of_ne hDproper
        have hRss : F \ D ⊂ F := by
          rw [Set.ssubset_iff_subset_ne]
          refine ⟨Set.diff_subset, ?_⟩
          obtain ⟨e, heD⟩ := hDne
          intro h
          have hmem : e ∈ F \ D := by rw [h]; exact hDF heD
          exact hmem.2 heD
        have hFfin : F.Finite := Set.toFinite _
        have hDcard : D.ncard < n := by
          rw [← hcard]; exact Set.ncard_lt_ncard hDss hFfin
        have hRcard : (F \ D).ncard < n := by
          rw [← hcard]; exact Set.ncard_lt_ncard hRss hFfin
        obtain ⟨𝒟D, hD1, hD2⟩ :=
          ih D.ncard hDcard D rfl (hDF.trans hFE) hDeven
        obtain ⟨𝒟R, hR1, hR2⟩ :=
          ih (F \ D).ncard hRcard (F \ D) rfl
            (fun e he => hFE he.1) (hFeven.sdiff hDF hDeven)
        refine ⟨𝒟D + 𝒟R, ?_, fun e => ?_⟩
        · intro C hC
          rw [Multiset.mem_add] at hC
          rcases hC with hC | hC
          · exact hD1 C hC
          · exact hR1 C hC
        · rw [Multiset.filter_add, Multiset.card_add, hD2 e, hR2 e]
          by_cases heF : e ∈ F
          · by_cases heD : e ∈ D
            · simp [heF, heD, show e ∉ F \ D from fun h => h.2 heD]
            · simp [heF, heD, show e ∈ F \ D from ⟨heF, heD⟩]
          · have heD : e ∉ D := fun h => heF (hDF h)
            simp [heF, heD, show e ∉ F \ D from fun h => heF h.1]

/-- Convenience form: decomposition of an even set with the count stated over
its membership. -/
theorem exists_cycle_decomposition' [Finite β] (G : Graph α β) {F : Set β}
    (hFE : F ⊆ E(G)) (hFeven : IsEven G F) :
    ∃ 𝒟 : Multiset (Set β), (∀ C ∈ 𝒟, IsCycle G C) ∧
      ∀ e, (𝒟.filter fun C => e ∈ C).card = if e ∈ F then 1 else 0 :=
  exists_cycle_decomposition G F.ncard F rfl hFE hFeven

end AffineCDC.Statement
