import ZFVP.ModelTheory.ShiftedCriticalEmbeddings
import ZFVP.ModelTheory.CriticalPointRestriction

/-! A fixed rank admits restrictions whose critical points run through
the critical sequence, obtained by taking images of one restricted graph. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem rankEmbedding_shifted_fixed_rank {k : ℕ} {δ f κ σ μ i : V}
    (hδ : Cn (k + 1) δ) (hf : IsCodedMembershipEmbedding (hierarchy δ) (hierarchy δ) f)
    (hc : IsCriticalPoint (hierarchy δ) f κ) [IsOrdinal σ] [IsOrdinal μ]
    (hσδ : σ ∈ δ) (hκσ : κ ∈ σ) (hμσ : μ ∈ σ)
    (hfixσ : f ‘ σ = σ) (hfixμ : f ‘ μ = μ) (hi : i ∈ (ω : V)) :
    ∃ g, IsCodedMembershipEmbedding (hierarchy σ) (hierarchy σ) g ∧
      IsCriticalPoint (hierarchy σ) g (criticalIterate f κ i) ∧ g ‘ μ = μ := by
  let := hδ.ordinal
  let := hc.ordinal
  let := hierarchy_transitive δ
  let := hierarchy_transitive σ
  have hσV := ordinal_subset_hierarchy δ σ hσδ
  have hAV := hierarchy_mem hσδ
  have hμA := ordinal_subset_hierarchy σ μ hμσ
  have hμV := (hierarchy_transitive δ).mem_trans hμA hAV
  have hκA := ordinal_subset_hierarchy σ κ hκσ
  have hnonempty : IsNonempty (hierarchy σ) := ⟨κ, hκA⟩
  have hr := rankEmbedding_restrict hδ hδ hf hAV hnonempty
  have hfA : f ‘ (hierarchy σ) = hierarchy σ := by
    rw [(rankEmbedding_value_hierarchy hδ hδ hf (show IsOrdinal σ from inferInstance) hσV).2, hfixσ]
  rw [hfA] at hr
  have hcr := hc.restrict hf.function ((hierarchy_transitive δ).transitive _ hAV) hκA
  have hrV := (hierarchy_transitive δ).mem_trans hr.function
    (function_mem_hierarchy_limit hδ.successor_closed hAV hAV)
  let p := embeddingPower (hierarchy δ) f i
  have hp := hf.power hi
  have hpσ : p ‘ σ = σ := embeddingPower_value_fixed hf hi hσV hfixσ
  have hpμ : p ‘ μ = μ := embeddingPower_value_fixed hf hi hμV hfixμ
  have hpA : p ‘ (hierarchy σ) = hierarchy σ := by
    rw [(rankEmbedding_value_hierarchy hδ hδ hp (show IsOrdinal σ from inferInstance) hσV).2, hpσ]
  have he := (rankElementaryMap_preserves_codedEmbedding hδ hδ hp.toElementaryMap
    ⟨hierarchy σ, hAV⟩ ⟨hierarchy σ, hAV⟩ ⟨f ↾ (hierarchy σ), hrV⟩).mpr hr
  change IsCodedMembershipEmbedding (p ‘ (hierarchy σ)) (p ‘ (hierarchy σ))
    (p ‘ (f ↾ (hierarchy σ))) at he
  rw [hpA] at he
  have himageTrans : IsTransitive (p ‘ (hierarchy σ)) := hpA.symm ▸ hierarchy_transitive σ
  let := himageTrans
  have hci := hp.value_criticalPoint hAV hAV hrV hr.function hcr
  rw [hpA, embeddingPower_value_criticalPoint hf hc.mem_domain hi] at hci
  refine ⟨p ‘ (f ↾ (hierarchy σ)), he, hci, ?_⟩
  have hv := hp.value_apply hrV hAV (IsFunction.of_mem hr.function)
    (domain_eq_of_mem_function hr.function) hμA
  let := IsFunction.of_mem hf.function
  have hrlambda : (f ↾ (hierarchy σ)) ‘ μ = μ := by
    rw [value_restrict (by rw [domain_eq_of_mem_function hf.function]; exact hμV) hμA, hfixμ]
  rwa [hpμ, hrlambda, hpμ] at hv

end ZFVP
