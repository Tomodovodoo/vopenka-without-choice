import ZFVP.ModelTheory.LastPointCorrectFixed
import ZFVP.ModelTheory.CriticalLimitRankBerkeley
import ZFVP.SetTheory.LeastChoicelessCofinality

/-! A critical point strictly below an uncountable-cofinality last point
produces a nonzero rank-Berkeley cardinal above any lower critical bound. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem rankEmbedding_lastPoint_rankBerkeley {n k l : ℕ} {θ η f κ α : V}
    (hθ : Cn (k + 1) θ) (hη : Cn (l + 1) η)
    (hf : IsCodedMembershipEmbedding (hierarchy θ) (hierarchy η) f)
    (hc : IsCriticalPoint (hierarchy θ) f κ) (hακ : α ∈ κ)
    (hκγ : κ ∈ lastPoint θ f) (hγθ : lastPoint θ f ∈ θ)
    (hCn : CnCofinal (n + 2) (lastPoint θ f))
    (hno : ∀ g, ¬IsCofinalMap (lastPoint θ f) (ω : V) g) :
    ∃ μ : V, α ∈ μ ∧ IsNonzeroRankBerkeley μ := by
  let := hθ.ordinal
  let := hη.ordinal
  let := hc.ordinal
  let := lastPoint_ordinal θ f
  let := hierarchy_transitive θ
  let := hierarchy_transitive η
  obtain ⟨β, hβγ, hκβ, hfixβ⟩ := rankEmbedding_fixed_cofinal_lastPoint hθ hη hf hκγ
  let : IsOrdinal β := IsOrdinal.of_mem hβγ
  obtain ⟨δ, hβδ, hδγ, hδ, hfixδ⟩ := rankEmbedding_correct_fixed_above hθ hη hf hγθ hCn hno hβγ
  let := hδ.ordinal
  let := hierarchy_transitive δ
  have hδθ := IsOrdinal.toIsTransitive.mem_trans hδγ hγθ
  have hδV := ordinal_subset_hierarchy θ δ hδθ
  have hκδ := IsOrdinal.toIsTransitive.mem_trans hκβ hβδ
  have hκA := ordinal_subset_hierarchy δ κ hκδ
  have hβA := ordinal_subset_hierarchy δ β hβδ
  have hr := rankEmbedding_restrict hθ hη hf (hierarchy_mem hδθ) ⟨κ, hκA⟩
  rw [(rankEmbedding_value_hierarchy hθ hη hf hδ.ordinal hδV).2, hfixδ] at hr
  have hcr := hc.restrict hf.function ((hierarchy_transitive θ).transitive _ (hierarchy_mem hδθ)) hκA
  let g := f ↾ (hierarchy δ)
  let := IsFunction.of_mem hf.function
  have hgβ : g ‘ β = β := by
    rw [value_restrict (by
      rw [domain_eq_of_mem_function hf.function]
      exact (hierarchy_transitive θ).mem_trans hβA (hierarchy_mem hδθ)) hβA, hfixβ]
  have hlim := CriticalSequence.limit_mem_of_fixed_bound hδ hr hcr
    (show IsOrdinal β from inferInstance) hβA hgβ hκβ
  have hκlim : κ ∈ criticalLimit g κ := by
    simpa using CriticalSequence.iterate_mem_limit hδ hr hcr (by simp : (0 : V) ∈ ω)
  let := CriticalSequence.limit_ordinal hδ hr hcr
  exact ⟨criticalLimit g κ, IsOrdinal.toIsTransitive.mem_trans hακ hκlim,
    CriticalSequence.limit_nonzeroRankBerkeley hδ hr hcr hlim⟩

theorem leastChoiceless_rankBerkeley_of_critical_below {n : ℕ} {α γ θ η f κ : V}
    (hγ : IsLeastOrdinal (IsAlphaChoicelessExtendible (n + 1) α) γ) (hωα : (ω : V) ⊆ α)
    (hθ : Cn (n + 2) θ) (hη : Cn (n + 1) η)
    (hf : IsCodedMembershipEmbedding (hierarchy θ) (hierarchy η) f)
    (hc : IsCriticalPoint (hierarchy θ) f κ) (hακ : α ∈ κ)
    (hκγ : κ ∈ γ) (hγθ : γ ∈ θ) (heq : lastPoint θ f = γ) :
    ∃ μ : V, α ∈ μ ∧ IsNonzeroRankBerkeley μ := by
  apply rankEmbedding_lastPoint_rankBerkeley hθ hη hf hc hακ (heq.symm ▸ hκγ) (heq.symm ▸ hγθ)
    (heq.symm ▸ leastChoiceless_cnCofinal hγ)
  intro g
  rw [heq]
  exact leastChoiceless_no_ordinal_cofinalMap hγ hωα

end ZFVP
