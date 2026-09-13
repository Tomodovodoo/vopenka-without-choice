import ZFVP.SetTheory.NaturalIteration
import ZFVP.SetTheory.FiniteCofinality
import ZFVP.SetTheory.FormulaReflection

/-! The supremum of an internally coded, strictly increasing omega
iteration of ordinals has internal cofinality omega. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem ordinalIteration_limit (F : V → V) (hF : ℒₛₑₜ-function₁ F) (ξ : V) [IsOrdinal ξ]
    (hstep : ∀ x, IsOrdinal x → IsOrdinal (F x) ∧ x ∈ F x) :
    ∃ δ : V, IsOrdinal δ ∧ ξ ∈ δ ∧ internalCofinality δ = ω ∧
      (∀ n ∈ (ω : V), naturalIteration F hF ξ n ∈ δ) ∧
      (∀ x ∈ δ, ∃ n ∈ (ω : V), x ∈ naturalIteration F hF ξ n) := by
  let a := naturalIteration F hF ξ
  have ha (n : V) (hn : n ∈ (ω : V)) : IsOrdinal (a n) :=
    naturalIteration_invariant F hF ξ IsOrdinal (by definability) inferInstance
      (fun x hx ↦ (hstep x hx).1) n hn
  have hinc (n : V) (hn : n ∈ (ω : V)) : a n ∈ a (succ n) := by
    change a n ∈ naturalIteration F hF ξ (succ n)
    rw [naturalIteration_succ F hF ξ hn]
    exact (hstep _ (ha n hn)).2
  let f := naturalIterationGraph F hF ξ
  have hval (n : V) (hn : n ∈ (ω : V)) : f ‘ n = a n := naturalIterationGraph_value F hF ξ hn
  let δ := ⋃ˢ range f
  have hord : IsOrdinal δ := IsOrdinal.sUnion (by
    intro y hy
    obtain ⟨n, hny⟩ := mem_range_iff.mp hy
    have hn : n ∈ (ω : V) := by
      simpa only [f, domain_naturalIterationGraph] using mem_domain_of_kpair_mem hny
    rw [← value_eq_of_kpair_mem hny, hval n hn]
    exact ha n hn)
  let := hord
  have harange (n : V) (hn : n ∈ (ω : V)) : a n ∈ range f := by
    rw [← hval n hn]
    exact mem_range_of_kpair_mem (kpair_value_mem (by
      simpa only [f, domain_naturalIterationGraph] using hn))
  have hstage (n : V) (hn : n ∈ (ω : V)) : a n ∈ δ :=
    mem_sUnion_iff.mpr ⟨a (succ n), harange _ (ω_succ_closed hn), hinc n hn⟩
  have hcof (x : V) (hx : x ∈ δ) : ∃ n ∈ (ω : V), x ∈ a n := by
    obtain ⟨y, hy, hxy⟩ := mem_sUnion_iff.mp hx
    obtain ⟨n, hny⟩ := mem_range_iff.mp hy
    have hn : n ∈ (ω : V) := by
      simpa only [f, domain_naturalIterationGraph] using mem_domain_of_kpair_mem hny
    refine ⟨n, hn, ?_⟩
    rw [← hval n hn, value_eq_of_kpair_mem hny]
    exact hxy
  have hξδ : ξ ∈ δ := by
    simpa only [a, naturalIteration_zero] using hstage 0 (by simp)
  have hs : ∀ x ∈ δ, succ x ∈ δ := by
    intro x hx
    obtain ⟨n, hn, hxn⟩ := hcof x hx
    let := ha n hn
    let := IsOrdinal.of_mem hxn
    have hsub : succ x ⊆ a n := by
      intro z hz
      rcases mem_succ_iff.mp hz with rfl | hz
      · exact hxn
      · exact IsOrdinal.toIsTransitive.mem_trans hz hxn
    exact ordinal_mem_of_subset_mem hsub (hstage n hn)
  have hcf : IsCofinalMap δ (ω : V) f := by
    refine ⟨definableGraph_mem_function_of_mapsTo _ _ _ _ hstage, ?_⟩
    intro x hx
    obtain ⟨n, hn, hxn⟩ := hcof x hx
    refine ⟨n, hn, ?_⟩
    rw [hval n hn]
    let := ha n hn
    exact IsOrdinal.toIsTransitive.transitive _ hxn
  have hzero : (0 : V) ∈ δ := ordinal_mem_of_subset_mem (empty_subset ξ) hξδ
  exact ⟨δ, hord, hξδ, SetTheory.subset_antisymm (internalCofinality_minimal hcf)
    (infinite_cofinality_of_succ_closed δ hzero hs), hstage, hcof⟩

end ZFVP
