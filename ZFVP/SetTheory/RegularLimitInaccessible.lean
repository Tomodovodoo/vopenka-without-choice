import ZFVP.SetTheory.RegularCofinalSurjection
import ZFVP.SetTheory.ChoicelessInaccessibleRank

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem regular_limit_of_inaccessibles {γ : V} (hγ : IsRegularCardinal γ)
    (hcof : ∀ α ∈ γ, ∃ κ ∈ γ, IsChoicelessInaccessible κ ∧ α ∈ κ) :
    IsChoicelessInaccessible γ := by
  let := hγ.1.1
  obtain ⟨κ₀, hκ₀γ, hκ₀, _⟩ := hcof 0 (hγ.2.1 _ (by simp))
  refine ⟨inferInstance, IsOrdinal.toIsTransitive.mem_trans hκ₀.2.1 hκ₀γ, ?_⟩
  intro α hα f hf
  obtain ⟨κ, hκγ, hκ, hακ⟩ := hcof α hα
  let := hκ.1
  let := IsOrdinal.of_mem hακ
  obtain ⟨g, hg, hgr⟩ := hf.surjection_of_regular hγ
  have hκn : IsNonempty κ := ⟨ω, hκ.2.1⟩
  obtain ⟨r, hr, hrr⟩ := surjection_of_injection
    (cardLE_of_subset (IsOrdinal.toIsTransitive.transitive _ hκγ)) hκn
  have hc := compose_function hg hr
  have hcr := range_compose_surjective hg hr hgr hrr
  exact hκ.no_rank_cofinalMap (hierarchy_mem hακ)
    (cofinalMap_precompose_surjection (identity_isCofinalMap κ) hc hcr)

/-- The noninaccessible branch at a limit of inaccessibles is singular in ZF. -/
theorem cofinality_mem_of_noninaccessible_limit {γ : V} [IsOrdinal γ]
    (hω : (ω : V) ⊆ γ)
    (hcof : ∀ α ∈ γ, ∃ κ ∈ γ, IsChoicelessInaccessible κ ∧ α ∈ κ)
    (hn : ¬IsChoicelessInaccessible γ) : internalCofinality γ ∈ γ := by
  rcases IsOrdinal.subset_iff.mp (internalCofinality_subset γ) with he | hlt
  · exact False.elim (hn (regular_limit_of_inaccessibles
      ⟨he ▸ internalCofinality_initial γ, hω, he⟩ hcof))
  · exact hlt

end ZFVP
