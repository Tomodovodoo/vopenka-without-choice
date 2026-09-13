import ZFVP.SetTheory.Cofinality

/-! Bounds for noncofinal maps into an ordinal, with arbitrary set domain. -/

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem map_not_cofinal_bounded {α D f : V} [IsOrdinal α]
    (hf : f ∈ α ^ D) (hNo : ¬IsCofinalMap α D f) :
    ∃ ξ ∈ α, ∀ i ∈ D, f ‘ i ∈ ξ := by
  classical
  have hn : ¬∀ ξ ∈ α, ∃ i ∈ D, ξ ⊆ f ‘ i := fun h ↦ hNo ⟨hf, h⟩
  push Not at hn
  obtain ⟨ξ, hξ, hbound⟩ := hn
  refine ⟨ξ, hξ, ?_⟩
  intro i hi
  have : IsOrdinal ξ := IsOrdinal.of_mem hξ
  have : IsOrdinal (f ‘ i) := IsOrdinal.of_mem (function_value_mem hf hi)
  exact IsOrdinal.mem_iff_subset_and_not_subset.mpr
    ⟨(IsOrdinal.subset_or_supset (f ‘ i) ξ).resolve_right (hbound i hi), hbound i hi⟩

theorem union_range_mem_of_not_cofinal {α D f : V} [IsOrdinal α]
    (hf : f ∈ α ^ D) (hNo : ¬IsCofinalMap α D f) : ⋃ˢ range f ∈ α := by
  have : IsFunction f := IsFunction.of_mem hf
  have : IsOrdinal (⋃ˢ range f) := IsOrdinal.sUnion
    (fun x hx ↦ IsOrdinal.of_mem (range_subset_of_mem_function hf x hx))
  obtain ⟨ξ, hξ, hbound⟩ := map_not_cofinal_bounded hf hNo
  have : IsOrdinal ξ := IsOrdinal.of_mem hξ
  have hs : ⋃ˢ range f ⊆ ξ := by
    intro x hx
    obtain ⟨y, hy, hxy⟩ := mem_sUnion_iff.mp hx
    obtain ⟨i, hiy⟩ := mem_range_iff.mp hy
    have hi : i ∈ D := domain_eq_of_mem_function hf ▸ mem_domain_of_kpair_mem hiy
    have hyξ : y ∈ ξ := value_eq_of_kpair_mem hiy ▸ hbound i hi
    exact IsOrdinal.toIsTransitive.transitive y hyξ x hxy
  rcases IsOrdinal.subset_iff.mp hs with heq | hlt
  · exact heq ▸ hξ
  · exact IsOrdinal.toIsTransitive.transitive ξ hξ _ hlt

end ZFVP
