import ZFVP.ModelTheory.EmbeddingPowers
import ZFVP.ModelTheory.CriticalChainInternalZF

/-! Restricted composition powers are elementary graphs inside the critical limit rank. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem IsCriticalPoint.of_fixed_below {A f κ : V} (hκ : IsOrdinal κ) (hmem : κ ∈ A)
    (hmoved : f ‘ κ ≠ κ) (hfix : ∀ α ∈ κ, f ‘ α = α) : IsCriticalPoint A f κ := by
  let := hκ
  refine ⟨hκ, ⟨hmem, hmoved⟩, ?_⟩
  intro α hα hαm
  let := hα
  rcases IsOrdinal.mem_trichotomy α κ with hlt | he | hgt
  · exact False.elim (hαm.2 (hfix α hlt))
  · exact subset_of_eq he.symm
  · exact IsOrdinal.toIsTransitive.transitive κ hgt

noncomputable def criticalPowerRestriction (δ f κ s t : V) : V :=
  (embeddingPower (hierarchy δ) f t) ↾ (hierarchy (criticalIterate f κ s))

namespace CriticalSequence

variable {k : ℕ} {δ f κ : V} (hδ : Cn (k + 1) δ)
  (h : IsCodedMembershipEmbedding (hierarchy δ) (hierarchy δ) f)
  (hκ : IsCriticalPoint (hierarchy δ) f κ)

include hδ h hκ

theorem criticalPoint_lt_iterate {n : V} (hn : n ∈ (ω : V)) (hne : n ≠ 0) :
    κ ∈ criticalIterate f κ n := by
  let := hδ.ordinal
  let := hierarchy_transitive δ
  let := hκ.ordinal
  rcases internalNatural_cases hn with he | ⟨p, hp, rfl⟩
  · exact False.elim (hne he)
  · let := (iterate_spec hδ h hκ hp).1
    have hsub := (h.power hp).ordinal_subset_value hκ.ordinal hκ.mem_domain
    rw [embeddingPower_value_criticalPoint h hκ.mem_domain hp] at hsub
    let := (iterate_spec hδ h hκ (ω_succ_closed hp)).1
    rcases IsOrdinal.subset_iff.mp hsub with he | hlt
    · exact (congrArg (fun x : V ↦ x ∈ criticalIterate f κ (succ p)) he).mpr
        (iterate_increasing hδ h hκ hp)
    · exact IsOrdinal.toIsTransitive.mem_trans hlt (iterate_increasing hδ h hκ hp)

theorem power_restriction_elementary {s t : V} (hs : s ∈ (ω : V)) (ht : t ∈ (ω : V)) :
    IsCodedMembershipEmbedding (hierarchy (criticalIterate f κ s))
      (hierarchy (criticalIterate f κ (ordinalAdd s t))) (criticalPowerRestriction δ f κ s t) := by
  have hα := iterate_spec hδ h hκ hs
  have hne := (successive_elementaryInclusion hδ h hκ hs).source_nonempty
  have hp := h.power ht
  have he := rankEmbedding_restrict hδ hδ hp (hδ.hierarchy_closed hα.1 hα.2.1) hne
  rw [(rankEmbedding_value_hierarchy hδ hδ hp hα.1 hα.2.1).2,
    embeddingPower_value_criticalIterate h hκ.mem_domain hs ht] at he
  exact he

theorem power_restriction_mem_limit {s t : V} (hs : s ∈ (ω : V)) (ht : t ∈ (ω : V)) :
    criticalPowerRestriction δ f κ s t ∈ hierarchy (criticalLimit f κ) := by
  let := limit_ordinal hδ h hκ
  let := hierarchy_transitive (criticalLimit f κ)
  have hclosed : ∀ β ∈ criticalLimit f κ, succ β ∈ criticalLimit f κ :=
    fun _ ↦ limit_succ_closed hδ h hκ
  have hf := (power_restriction_elementary hδ h hκ hs ht).function
  exact (hierarchy_transitive (criticalLimit f κ)).mem_trans hf
    (function_mem_hierarchy_limit hclosed (hierarchy_mem (iterate_mem_limit hδ h hκ hs))
      (hierarchy_mem (iterate_mem_limit hδ h hκ (ordinalAdd_natural hs ht))))

theorem power_restriction_value {s t x : V} (hs : s ∈ (ω : V)) (ht : t ∈ (ω : V))
    (hx : x ∈ hierarchy (criticalIterate f κ s)) :
    (criticalPowerRestriction δ f κ s t) ‘ x = (embeddingPower (hierarchy δ) f t) ‘ x := by
  let := hδ.ordinal
  let := IsFunction.of_mem (h.power ht).function
  have hxδ := (hierarchy_transitive δ).mem_trans hx
    (hδ.hierarchy_closed (iterate_spec hδ h hκ hs).1 (iterate_spec hδ h hκ hs).2.1)
  exact value_restrict (by rw [domain_eq_of_mem_function (h.power ht).function]; exact hxδ) hx

theorem power_restriction_criticalPoint {s t : V} (hs : s ∈ (ω : V)) (ht : t ∈ (ω : V))
    (hs0 : s ≠ 0) (ht0 : t ≠ 0) :
    IsCriticalPoint (hierarchy (criticalIterate f κ s)) (criticalPowerRestriction δ f κ s t) κ := by
  let := hδ.ordinal
  let := hierarchy_transitive δ
  let := (iterate_spec hδ h hκ hs).1
  let := hierarchy_transitive (criticalIterate f κ s)
  have hκs := ordinal_subset_hierarchy _ κ (criticalPoint_lt_iterate hδ h hκ hs hs0)
  apply IsCriticalPoint.of_fixed_below hκ.ordinal hκs
  · rw [power_restriction_value hδ h hκ hs ht hκs,
      embeddingPower_value_criticalPoint h hκ.mem_domain ht]
    intro he
    have hm := criticalPoint_lt_iterate hδ h hκ ht ht0
    rw [he] at hm
    exact mem_irrefl κ hm
  · intro α hα
    have hαs := (hierarchy_transitive (criticalIterate f κ s)).mem_trans hα hκs
    rw [power_restriction_value hδ h hκ hs ht hαs]
    exact embeddingPower_value_fixed h ht
      ((hierarchy_transitive δ).mem_trans hα hκ.mem_domain) (hκ.fixed_below hα)

end CriticalSequence

end ZFVP
