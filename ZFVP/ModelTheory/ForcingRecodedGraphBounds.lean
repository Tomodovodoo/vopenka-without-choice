import ZFVP.ModelTheory.ForcingRecodedCode

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable {θ s Q T m i j : V}

private theorem bounded_compose_between {A B C D f g r : V}
    (hf : f ∈ B ^ A) (hg : g ∈ D ^ C) :
    compose (compose f r) g ⊆ A ×ˢ D := by
  intro z hz
  obtain ⟨x, y, w, hxy, hyw, rfl⟩ := mem_compose_iff.mp hz
  obtain ⟨a, hxa, _⟩ := kpair_mem_compose_iff.mp hxy
  exact kpair_mem_iff.mpr ⟨(mem_of_mem_functions hf hxa).1, (mem_of_mem_functions hg hyw).2⟩

private theorem function_value_mem_or_empty {A B f : V} (hf : f ∈ B ^ A) (x : V) :
    f ‘ x ∈ B ∪ ({∅} : V) := by
  classical
  by_cases hx : x ∈ A
  · exact mem_union_iff.mpr (Or.inl (function_value_mem hf hx))
  · rw [value_eq_empty_of_not_mem_domain (by rwa [domain_eq_of_mem_function hf])]
    exact mem_union_iff.mpr (Or.inr (by simp))

variable (hm : ∀ i ∈ θ, IsForcingIsomorphism ((forcingCodeP s) ‘ i) ((forcingCodeR s) ‘ i)
  (Q ‘ i) (T ‘ i) (m ‘ i))
include hm in
 theorem forcingRecodedProjections_graph_bound (hi : i ∈ θ) (hj : j ∈ θ) :
    (forcingRecodedProjections θ s m) ‘ ⟨i, j⟩ₖ ⊆ (Q ‘ j) ×ˢ (Q ‘ i) := by
  rw [forcingRecodedProjections_value hi hj]
  exact bounded_compose_between (hm j hj).inverse_maps (hm i hi).1

include hm in
 theorem forcingRecodedSections_graph_bound (hi : i ∈ θ) (hj : j ∈ θ) :
    (forcingRecodedSections θ s m) ‘ ⟨i, j⟩ₖ ⊆ (Q ‘ i) ×ˢ (Q ‘ j) := by
  rw [forcingRecodedSections_value hi hj]
  exact bounded_compose_between (hm i hi).inverse_maps (hm j hj).1

include hm in
 theorem forcingRecodedLifts_graph_bound (hi : i ∈ θ) (hj : j ∈ θ) :
    (forcingRecodedLifts θ s Q m) ‘ ⟨i, j⟩ₖ ⊆
      ((Q ‘ j) ×ˢ (Q ‘ i)) ×ˢ ((Q ‘ j) ∪ ({∅} : V)) := by
  rw [forcingRecodedLifts, value_definableGraph _ _ _ (kpair_mem_iff.mpr ⟨hi, hj⟩)]
  simp only [forcingRecodedLiftMap, kpair.π₁_kpair, kpair.π₂_kpair]
  intro z hz
  obtain ⟨w, hw, rfl⟩ := mem_definableGraph_iff _ _ _ _ |>.mp hz
  exact kpair_mem_iff.mpr ⟨hw, function_value_mem_or_empty (hm j hj).1 _⟩

end ZFVP
