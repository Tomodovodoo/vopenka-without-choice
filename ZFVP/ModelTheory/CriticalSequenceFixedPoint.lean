import ZFVP.ModelTheory.CriticalSequence
import ZFVP.ModelTheory.EmbeddingCofinality

/-! A critical-sequence limit in the source is fixed, and supports an elementary restriction. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace CriticalSequence

variable {k : ℕ} {δ f κ : V} (hδ : Cn (k + 1) δ)
  (h : IsCodedMembershipEmbedding (hierarchy δ) (hierarchy δ) f)
  (hκ : IsCriticalPoint (hierarchy δ) f κ)

include hδ h hκ

theorem sequence_mem_domain (hlim : criticalLimit f κ ∈ hierarchy δ) :
    criticalSequence f κ ∈ hierarchy δ := by
  let := hδ.ordinal
  have hω : (ω : V) ∈ hierarchy δ := ((cn_successor_iff k δ).mp hδ).2.support.omega_mem
  exact (hierarchy_transitive δ).mem_trans (sequence_function hδ h hκ)
    (function_mem_hierarchy_limit hδ.successor_closed hω hlim)

theorem image_sequence_value (hlim : criticalLimit f κ ∈ hierarchy δ)
    {n : V} (hn : n ∈ (ω : V)) :
    (f ‘ (criticalSequence f κ)) ‘ n = criticalIterate f κ (succ n) := by
  let : IsSequenceSupport (hierarchy δ) := ((cn_successor_iff k δ).mp hδ).2.support
  have hv := h.value_apply (sequence_mem_domain hδ h hκ hlim) IsCodingSupport.omega_mem
    (criticalSequence_isFunction f κ) (criticalSequence_domain f κ) hn
  rw [h.value_natural hn, criticalSequence_value f κ hn] at hv
  exact hv.trans (criticalIterate_succ f κ hn).symm

theorem limit_fixed (hlim : criticalLimit f κ ∈ hierarchy δ) :
    f ‘ (criticalLimit f κ) = criticalLimit f κ := by
  let : IsSequenceSupport (hierarchy δ) := ((cn_successor_iff k δ).mp hδ).2.support
  let := limit_ordinal hδ h hκ
  have hmap := h.value_cofinalMap (sequence_mem_domain hδ h hκ hlim) IsCodingSupport.omega_mem
    hlim (cofinal hδ h hκ)
  rw [h.value_omega IsCodingSupport.omega_mem] at hmap
  apply SetTheory.subset_antisymm
  · intro x hx
    obtain ⟨n, hn, hxn⟩ := hmap.2 x hx
    rw [image_sequence_value hδ h hκ hlim hn] at hxn
    let := (iterate_spec hδ h hκ (ω_succ_closed hn)).1
    let := h.value_ordinal (limit_ordinal hδ h hκ) hlim
    let := IsOrdinal.of_mem hx
    rcases IsOrdinal.subset_iff.mp hxn with he | hl
    · exact he.symm ▸ iterate_mem_limit hδ h hκ (ω_succ_closed hn)
    · exact IsOrdinal.toIsTransitive.mem_trans hl (iterate_mem_limit hδ h hκ (ω_succ_closed hn))
  · exact h.ordinal_subset_value (limit_ordinal hδ h hκ) hlim

theorem iterate_below_fixed {β : V} (hβ : β ∈ hierarchy δ) (hfix : f ‘ β = β)
    (hκβ : κ ∈ β) {n : V} (hn : n ∈ (ω : V)) : criticalIterate f κ n ∈ β := by
  let := hδ.ordinal
  let := hierarchy_transitive δ
  have hi : ∀ n ∈ (ω : V), criticalIterate f κ n ∈ β := by
    apply naturalNumber_induction (fun n ↦ criticalIterate f κ n ∈ β) (by definability)
    · simpa using hκβ
    · intro n hn ih
      rw [criticalIterate_succ f κ hn, ← hfix]
      exact (h.value_mem_iff (iterate_spec hδ h hκ hn).2.1 hβ).mpr ih
  exact hi n hn

theorem limit_below_fixed {β : V} (hβord : IsOrdinal β) (hβ : β ∈ hierarchy δ)
    (hfix : f ‘ β = β) (hκβ : κ ∈ β) : criticalLimit f κ ⊆ β := by
  let := hβord
  intro x hx
  obtain ⟨n, hn, hxn⟩ := (mem_criticalLimit_iff f κ x).mp hx
  exact IsOrdinal.toIsTransitive.mem_trans hxn (iterate_below_fixed hδ h hκ hβ hfix hκβ hn)

theorem limit_mem_of_fixed_bound {β : V} (hβord : IsOrdinal β) (hβ : β ∈ hierarchy δ)
    (hfix : f ‘ β = β) (hκβ : κ ∈ β) : criticalLimit f κ ∈ hierarchy δ := by
  let := hδ.ordinal
  let := hβord
  let := limit_ordinal hδ h hκ
  rw [ordinal_mem_hierarchy_iff]
  have hβδ := ordinal_mem_hierarchy_iff.mp hβ
  rcases IsOrdinal.subset_iff.mp (limit_below_fixed hδ h hκ hβord hβ hfix hκβ) with he | hl
  · exact he.symm ▸ hβδ
  · exact IsOrdinal.toIsTransitive.mem_trans hl hβδ

theorem limit_restriction (hlim : criticalLimit f κ ∈ hierarchy δ) :
    IsCodedMembershipEmbedding (hierarchy (criticalLimit f κ)) (hierarchy (criticalLimit f κ))
      (f ↾ (hierarchy (criticalLimit f κ))) := by
  let := hκ.ordinal
  let := limit_ordinal hδ h hκ
  have hκlim : κ ∈ criticalLimit f κ := by
    simpa using iterate_mem_limit hδ h hκ (by simp : (0 : V) ∈ ω)
  have hne : IsNonempty (hierarchy (criticalLimit f κ)) := ⟨κ, ordinal_mem_hierarchy_iff.mpr hκlim⟩
  have hr := rankEmbedding_restrict hδ hδ h
    (hδ.hierarchy_closed (limit_ordinal hδ h hκ) hlim) hne
  rw [(rankEmbedding_value_hierarchy hδ hδ h (limit_ordinal hδ h hκ) hlim).2,
    limit_fixed hδ h hκ hlim] at hr
  exact hr

end CriticalSequence

end ZFVP
