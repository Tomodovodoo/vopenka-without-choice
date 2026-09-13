import ZFVP.SetTheory.CnExtendibleSmallEmbedding
import ZFVP.ModelTheory.CriticalLimitCardinal

/-! The small-embedding criterion itself supplies its initial-ordinal condition. -/

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem SmallEmbeddingCriterion.initial {n : ℕ} {δ : V}
    (h : SmallEmbeddingCriterion n δ) : IsInitialOrdinal δ := by
  obtain ⟨θ, h0θ, hθ, hall⟩ := h ∅ inferInstance
  obtain ⟨δ', θ', α', e, _, _, _, hθ', he, hc, heδ, _⟩ := hall ∅ h0θ
  have hδ' := rankEmbedding_criticalPoint_initial hθ' hθ he hc
  have hh := (rankEmbedding_initial_iff hθ' hθ he hc.mem_domain).mp hδ'
  rwa [heδ] at hh

theorem SmallEmbeddingCriterion.cnExtendible {k : ℕ} {δ : V}
    (h : SmallEmbeddingCriterion (k + 1) δ) : IsCnExtendible (k + 1) δ :=
  IsCnExtendible.of_smallEmbeddingCriterion h.initial h

end ZFVP
