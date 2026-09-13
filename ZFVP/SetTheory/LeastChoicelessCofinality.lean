import ZFVP.SetTheory.LeastChoicelessCn
import ZFVP.ModelTheory.LastPointCofinality

/-! Mohammd Proposition 6.5(iii): no cofinal map from a lower rank stage. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem leastChoiceless_no_rank_cofinalMap {n : ℕ} {α γ ξ g : V}
    (hγ : IsLeastOrdinal (IsAlphaChoicelessExtendible (n + 1) α) γ)
    [IsOrdinal ξ] (hξα : ξ ⊆ α) : ¬IsCofinalMap γ (hierarchy ξ) g := by
  let := hγ.1
  let := hγ.2.1.bound_ordinal
  obtain ⟨θ, η, f, κ, _, hγθ, hθ, _, hη, hf, hc, hακ, _, heq⟩ :=
    leastChoiceless_high_lastPoint_embeddings hγ γ
  let := hc.ordinal
  have hξκ := ordinal_mem_of_subset_mem hξα hακ
  have hA : hierarchy ξ ∈ hierarchy κ := hierarchy_mem hξκ
  rw [← heq]
  exact rankEmbedding_lastPoint_no_cofinalMap hθ hη hf hc (heq.symm ▸ hγθ) hA

theorem leastChoiceless_no_ordinal_cofinalMap {n : ℕ} {α γ ξ g : V}
    (hγ : IsLeastOrdinal (IsAlphaChoicelessExtendible (n + 1) α) γ)
    [IsOrdinal ξ] (hξα : ξ ⊆ α) : ¬IsCofinalMap γ ξ g := by
  let := hγ.1
  let := hγ.2.1.bound_ordinal
  obtain ⟨θ, η, f, κ, _, hγθ, hθ, _, hη, hf, hc, hακ, _, heq⟩ :=
    leastChoiceless_high_lastPoint_embeddings hγ γ
  let := hc.ordinal
  have hξκ := ordinal_mem_of_subset_mem hξα hακ
  rw [← heq]
  exact rankEmbedding_lastPoint_no_cofinalMap hθ hη hf hc (heq.symm ▸ hγθ)
    (ordinal_subset_hierarchy κ ξ hξκ)

theorem leastChoiceless_cofinality_gt {n : ℕ} {α γ : V}
    (hγ : IsLeastOrdinal (IsAlphaChoicelessExtendible (n + 1) α) γ) :
    α ∈ internalCofinality γ := by
  let := hγ.1
  let := hγ.2.1.bound_ordinal
  obtain ⟨g, hg⟩ := cofinalMap_exists γ
  rcases IsOrdinal.mem_trichotomy (internalCofinality γ) α with hl | he | hg'
  · exact False.elim (leastChoiceless_no_ordinal_cofinalMap hγ
      (IsOrdinal.toIsTransitive.transitive _ hl) hg)
  · exact False.elim (leastChoiceless_no_ordinal_cofinalMap hγ (subset_of_eq he) hg)
  · exact hg'

end ZFVP
