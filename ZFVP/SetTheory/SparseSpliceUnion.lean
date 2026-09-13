import ZFVP.SetTheory.SparseSplice

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem mem_sUnion_range_function_iff {f z : V} [IsFunction f] :
    z ∈ ⋃ˢ range f ↔ ∃ j ∈ domain f, z ∈ f ‘ j := by
  constructor
  · intro hz
    obtain ⟨p, hp, hz⟩ := mem_sUnion_iff.mp hz
    obtain ⟨j, hj⟩ := mem_range_iff.mp hp
    exact ⟨j, mem_domain_of_kpair_mem hj, (value_eq_of_kpair_mem hj).symm ▸ hz⟩
  · rintro ⟨j, hj, hz⟩
    exact mem_sUnion_iff.mpr ⟨f ‘ j, mem_range_of_kpair_mem (kpair_value_mem hj), hz⟩

theorem sparsePrefixReplace_sUnion_range {θ i a f g b : V}
    [IsOrdinal θ] [IsFunction f] [IsFunction g]
    (hf : domain f = θ) (hg : domain g = θ) (hi : i ∈ θ)
    (hearly : ∀ j ∈ θ, j ∈ i → domain (f ‘ j) ⊆ a ∧ g ‘ j ⊆ b)
    (hlate : ∀ j ∈ θ, i ⊆ j → g ‘ j = sparsePrefixReplace a (f ‘ j) b) :
    ⋃ˢ range g = sparsePrefixReplace a (⋃ˢ range f) b := by
  let := IsOrdinal.of_mem hi
  have hsplit : ∀ j ∈ θ, j ∉ i → i ⊆ j := by
    intro j hj hn
    let := IsOrdinal.of_mem hj
    rcases IsOrdinal.mem_trichotomy j i with h | rfl | h
    · exact (hn h).elim
    · exact subset_refl _
    · exact IsOrdinal.toIsTransitive.transitive _ h
  have hfm {j z : V} (hj : j ∈ θ) (hz : z ∈ f ‘ j) : z ∈ ⋃ˢ range f :=
    mem_sUnion_range_function_iff.mpr ⟨j, hf.symm ▸ hj, hz⟩
  have hgm {j z : V} (hj : j ∈ θ) (hz : z ∈ g ‘ j) : z ∈ ⋃ˢ range g :=
    mem_sUnion_range_function_iff.mpr ⟨j, hg.symm ▸ hj, hz⟩
  apply mem_ext
  intro z
  constructor
  · intro hz
    obtain ⟨j, hj, hz⟩ := mem_sUnion_range_function_iff.mp hz
    rw [hg] at hj
    by_cases hji : j ∈ i
    · exact mem_union_iff.mpr (Or.inl ((hearly j hj hji).2 z hz))
    · rw [hlate j hj (hsplit j hj hji)] at hz
      rcases mem_union_iff.mp hz with hz | hz
      · exact mem_union_iff.mpr (Or.inl hz)
      · obtain ⟨hz, x, hx, y, rfl⟩ := mem_restrict_iff.mp hz
        have hxf := hfm hj hz
        exact kpair_mem_sparsePrefixReplace_iff.mpr (Or.inr ⟨hxf, (mem_sdiff_iff.mp hx).2⟩)
  · intro hz
    rcases mem_union_iff.mp hz with hz | hz
    · apply hgm hi
      rw [hlate i hi (subset_refl _)]
      exact mem_union_iff.mpr (Or.inl hz)
    · obtain ⟨hz, x, hx, y, rfl⟩ := mem_restrict_iff.mp hz
      have hna := (mem_sdiff_iff.mp hx).2
      obtain ⟨j, hj, hz⟩ := mem_sUnion_range_function_iff.mp hz
      rw [hf] at hj
      have hji : j ∉ i := fun hji ↦ hna ((hearly j hj hji).1 x (mem_domain_of_kpair_mem hz))
      apply hgm hj
      rw [hlate j hj (hsplit j hj hji)]
      exact kpair_mem_sparsePrefixReplace_iff.mpr (Or.inr ⟨hz, hna⟩)

theorem sparsePrefixReplace_sUnion_range_restrictions {θ i a f g b d : V}
    [IsOrdinal θ] [IsFunction f] [IsFunction g]
    (hf : domain f = θ) (hg : domain g = θ) (hi : i ∈ θ)
    (hearly : ∀ j ∈ θ, j ∈ i → domain (f ‘ j) ⊆ a ∧ g ‘ j = b ↾ (d ‘ j))
    (hlate : ∀ j ∈ θ, i ⊆ j → g ‘ j = sparsePrefixReplace a (f ‘ j) b) :
    ⋃ˢ range g = sparsePrefixReplace a (⋃ˢ range f) b := by
  apply sparsePrefixReplace_sUnion_range hf hg hi ?_ hlate
  intro j hj hji
  refine ⟨(hearly j hj hji).1, ?_⟩
  rw [(hearly j hj hji).2]
  exact restrict_subset _ _

end ZFVP
