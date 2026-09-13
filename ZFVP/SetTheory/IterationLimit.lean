import ZFVP.SetTheory.MonotoneCofinality
import ZFVP.SetTheory.NaturalIteration

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem increasingIteration_limit {κ ξ : V} [IsOrdinal κ]
    (hω : (ω : V) ∈ internalCofinality κ) (F : V → V) (hF : ℒₛₑₜ-function₁ F)
    (hξ : ξ ∈ κ) (hstep : ∀ x ∈ κ, F x ∈ κ ∧ x ∈ F x) :
    ∃ δ ∈ κ, ξ ∈ δ ∧
      (∀ n ∈ (ω : V), naturalIteration F hF ξ n ∈ δ) ∧
      (∀ x ∈ δ, ∃ n ∈ (ω : V), x ∈ naturalIteration F hF ξ n) := by
  let a := naturalIteration F hF ξ
  have ha (n : V) (hn : n ∈ (ω : V)) : a n ∈ κ :=
    naturalIteration_invariant F hF ξ (fun x ↦ x ∈ κ) (by definability) hξ
      (fun x hx ↦ (hstep x hx).1) n hn
  have hinc (n : V) (hn : n ∈ (ω : V)) : a n ∈ a (succ n) := by
    change a n ∈ naturalIteration F hF ξ (succ n)
    rw [naturalIteration_succ F hF ξ hn]
    exact (hstep _ (ha n hn)).2
  let f := naturalIterationGraph F hF ξ
  have hf : f ∈ κ ^ (ω : V) := definableGraph_mem_function_of_mapsTo _ _ _ _ ha
  have hval (n : V) (hn : n ∈ (ω : V)) : f ‘ n = a n := naturalIterationGraph_value F hF ξ hn
  let δ := ⋃ˢ range f
  have hord : IsOrdinal δ := IsOrdinal.sUnion (fun x hx ↦ IsOrdinal.of_mem (range_subset_of_mem_function hf x hx))
  obtain ⟨ζ, hζ, hbound⟩ := map_below_cofinality_bounded hω hf
  have hδζ : δ ⊆ ζ := by
    intro x hx
    obtain ⟨y, hy, hxy⟩ := mem_sUnion_iff.mp hx
    obtain ⟨n, hny⟩ := mem_range_iff.mp hy
    have hn : n ∈ (ω : V) := domain_eq_of_mem_function hf ▸ mem_domain_of_kpair_mem hny
    have hyζ : y ∈ ζ := value_eq_of_kpair_mem hny ▸ hbound n hn
    have : IsOrdinal ζ := IsOrdinal.of_mem hζ
    exact IsOrdinal.toIsTransitive.transitive y hyζ x hxy
  have hδ : δ ∈ κ := by
    have : IsOrdinal ζ := IsOrdinal.of_mem hζ
    rcases IsOrdinal.subset_iff.mp hδζ with heq | hlt
    · exact heq ▸ hζ
    · exact IsOrdinal.toIsTransitive.transitive ζ hζ δ hlt
  have harange (n : V) (hn : n ∈ (ω : V)) : a n ∈ range f := by
    rw [← hval n hn]
    exact mem_range_of_kpair_mem (kpair_value_mem (by simpa only [domain_eq_of_mem_function hf] using hn))
  have haδ (n : V) (hn : n ∈ (ω : V)) : a n ∈ δ :=
    mem_sUnion_iff.mpr ⟨a (succ n), harange _ (ω_succ_closed hn), hinc n hn⟩
  refine ⟨δ, hδ, ?_, haδ, ?_⟩
  · simpa only [a, naturalIteration_zero] using haδ 0 (by simp)
  · intro x hx
    obtain ⟨y, hy, hxy⟩ := mem_sUnion_iff.mp hx
    obtain ⟨n, hny⟩ := mem_range_iff.mp hy
    have hn : n ∈ (ω : V) := domain_eq_of_mem_function hf ▸ mem_domain_of_kpair_mem hny
    refine ⟨n, hn, ?_⟩
    change x ∈ a n
    rw [← hval n hn, value_eq_of_kpair_mem hny]
    exact hxy

end ZFVP
