import ZFVP.ModelTheory.EmbeddingSupercompactBase
import ZFVP.SetTheory.ChoicelessExtendible

/-! Relative extendibility supplies the small embeddings required by
relative supercompactness at levels at least two. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem IsAlphaChoicelessExtendible.supercompact {n : ℕ} {α γ : V}
    (h : IsAlphaChoicelessExtendible (n + 2) α γ) :
    IsAlphaChoicelessSupercompact (n + 2) α γ := by
  let := h.ordinal
  refine ⟨h.ordinal, h.2.1, ?_⟩
  intro μ hμ hγμ a ha
  let := hμ.ordinal
  obtain ⟨θ, hμθ, hθ⟩ := cn_unbounded (n + 2) μ
  let := hθ.ordinal
  let := hierarchy_transitive θ
  have hγθ := IsOrdinal.toIsTransitive.mem_trans hγμ hμθ
  obtain ⟨η, f, κ, hη, hf, hc, hακ, hθimage⟩ := h.2.2 θ hθ hγθ
  let := hη.ordinal
  let := hierarchy_transitive η
  have hγV := ordinal_subset_hierarchy θ γ hγθ
  let := hf.value_ordinal h.ordinal hγV
  have hγimage : γ ∈ f ‘ γ := IsOrdinal.toIsTransitive.mem_trans hγθ hθimage
  have hmove : f ‘ γ ≠ γ := by
    intro he
    rw [he] at hγimage
    exact mem_irrefl γ hγimage
  have hκγ : κ ⊆ γ := hc.2.2 γ h.ordinal ⟨hγV, hmove⟩
  exact rankEmbedding_supercompactWitness_below_image hθ
    (hη.of_le (by omega : n + 1 ≤ n + 2)) hf hc hακ hκγ hγμ
    (IsOrdinal.toIsTransitive.mem_trans hμθ hθimage) hμθ hμ ha

end ZFVP
