import ZFVP.SetTheory.ChoicelessFailureClub
import ZFVP.ModelTheory.EmbeddingCnTransfer
import ZFVP.ModelTheory.CriticalPointRestriction

/-! The rank-restriction contradiction used in the forward Vopenka argument. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem choicelessFailureLimit_no_embedding {n : ℕ} {α β δ σ f κ : V}
    (hD : IsChoicelessFailureLimit (n + 1) α β)
    (hβ : Cn (n + 2) β) (hδ : Cn (n + 2) δ)
    (hf : IsCodedMembershipEmbedding (hierarchy β) (hierarchy δ) f)
    (hc : IsCriticalPoint (hierarchy β) f κ) (hακ : α ∈ κ)
    (hασ : α ∈ σ) (hσβ : σ ∈ β) (hm : β ⊆ f ‘ σ) : False := by
  let := hβ.ordinal
  let := hδ.ordinal
  let := hierarchy_transitive β
  let := hierarchy_transitive δ
  let := hc.ordinal
  let : IsOrdinal σ := IsOrdinal.of_mem hσβ
  have hσV := ordinal_subset_hierarchy β σ hσβ
  have hn : f ‘ σ ≠ σ := by
    intro he
    have hs := hm σ hσβ
    rw [he] at hs
    exact mem_irrefl σ hs
  have hκσ := hc.2.2 σ inferInstance ⟨hσV, hn⟩
  obtain ⟨μ, hμβ, hw⟩ := hD.2.2.2 σ hσβ hασ
  let := hw.1.ordinal
  let := hierarchy_transitive μ
  have hκμ : κ ∈ μ := ordinal_mem_of_subset_mem hκσ hw.2.1
  have hμV := ordinal_subset_hierarchy β μ hμβ
  have hCn := (rankEmbedding_cn_iff hβ hδ hf hμV).mp hw.1
  have hr := rankEmbedding_restrict hβ hδ hf (hierarchy_mem hμβ)
    ⟨ω, ordinal_subset_hierarchy μ _ hw.1.omega_lt⟩
  rw [(rankEmbedding_value_hierarchy hβ hδ hf hw.1.ordinal hμV).2] at hr
  have hcr := hc.restrict hf.function
    ((hierarchy_transitive β).transitive _ (hierarchy_mem hμβ))
    (ordinal_subset_hierarchy μ κ hκμ)
  apply hw.2.2
  refine ⟨f ‘ μ, f ↾ (hierarchy μ), κ, hCn, hr, hcr, hακ, ?_⟩
  let := IsFunction.of_mem hf.function
  rw [value_restrict (by rw [domain_eq_of_mem_function hf.function]; exact hσV)
    (ordinal_subset_hierarchy μ σ hw.2.1)]
  exact hm μ hμβ

end ZFVP
