import ZFVP.ModelTheory.EmbeddingCriticalPointImage

/-! Images of restricted powers move the critical point to any critical-sequence stage. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def shiftedCriticalEmbedding (δ f κ s t i : V) : V :=
  (embeddingPower (hierarchy δ) f i) ‘ (criticalPowerRestriction δ f κ s t)

namespace CriticalSequence

variable {k : ℕ} {δ f κ : V} (hδ : Cn (k + 1) δ)
  (h : IsCodedMembershipEmbedding (hierarchy δ) (hierarchy δ) f)
  (hκ : IsCriticalPoint (hierarchy δ) f κ)

include hδ h hκ

theorem power_value_hierarchy {s i : V} (hs : s ∈ (ω : V)) (hi : i ∈ (ω : V)) :
    (embeddingPower (hierarchy δ) f i) ‘ (hierarchy (criticalIterate f κ s)) =
      hierarchy (criticalIterate f κ (ordinalAdd s i)) := by
  rw [(rankEmbedding_value_hierarchy hδ hδ (h.power hi)
    (iterate_spec hδ h hκ hs).1 (iterate_spec hδ h hκ hs).2.1).2,
    embeddingPower_value_criticalIterate h hκ.mem_domain hs hi]

theorem power_value_mem_limit (hlim : criticalLimit f κ ∈ hierarchy δ)
    {i x : V} (hi : i ∈ (ω : V)) (hx : x ∈ hierarchy (criticalLimit f κ)) :
    (embeddingPower (hierarchy δ) f i) ‘ x ∈ hierarchy (criticalLimit f κ) := by
  let := hδ.ordinal
  let := limit_ordinal hδ h hκ
  have hV := hδ.hierarchy_closed (limit_ordinal hδ h hκ) hlim
  have hxδ := (hierarchy_transitive δ).mem_trans hx hV
  have hm := ((h.power hi).value_mem_iff hxδ hV).mpr hx
  have he := (rankEmbedding_value_hierarchy hδ hδ (h.power hi)
    (limit_ordinal hδ h hκ) hlim).2
  rw [embeddingPower_value_fixed h hi hlim (limit_fixed hδ h hκ hlim)] at he
  rw [he] at hm
  exact hm

theorem shifted_mem_limit (hlim : criticalLimit f κ ∈ hierarchy δ)
    {s t i : V} (hs : s ∈ (ω : V)) (ht : t ∈ (ω : V)) (hi : i ∈ (ω : V)) :
    shiftedCriticalEmbedding δ f κ s t i ∈ hierarchy (criticalLimit f κ) :=
  power_value_mem_limit hδ h hκ hlim hi (power_restriction_mem_limit hδ h hκ hs ht)

theorem shifted_elementary (hlim : criticalLimit f κ ∈ hierarchy δ)
    {s t i : V} (hs : s ∈ (ω : V)) (ht : t ∈ (ω : V)) (hi : i ∈ (ω : V)) :
    IsCodedMembershipEmbedding (hierarchy (criticalIterate f κ (ordinalAdd s i)))
      (hierarchy (criticalIterate f κ (ordinalAdd (ordinalAdd s t) i)))
      (shiftedCriticalEmbedding δ f κ s t i) := by
  let := hδ.ordinal
  have hA := hδ.hierarchy_closed (iterate_spec hδ h hκ hs).1 (iterate_spec hδ h hκ hs).2.1
  have hB := hδ.hierarchy_closed (iterate_spec hδ h hκ (ordinalAdd_natural hs ht)).1
    (iterate_spec hδ h hκ (ordinalAdd_natural hs ht)).2.1
  have heδ := (hierarchy_transitive δ).mem_trans (power_restriction_mem_limit hδ h hκ hs ht)
    (hδ.hierarchy_closed (limit_ordinal hδ h hκ) hlim)
  have hm := (rankElementaryMap_preserves_codedEmbedding hδ hδ (h.power hi).toElementaryMap
    ⟨_, hA⟩ ⟨_, hB⟩ ⟨_, heδ⟩).mpr (power_restriction_elementary hδ h hκ hs ht)
  change IsCodedMembershipEmbedding ((embeddingPower (hierarchy δ) f i) ‘ _)
    ((embeddingPower (hierarchy δ) f i) ‘ _) (shiftedCriticalEmbedding δ f κ s t i) at hm
  rw [power_value_hierarchy hδ h hκ hs hi,
    power_value_hierarchy hδ h hκ (ordinalAdd_natural hs ht) hi] at hm
  exact hm

theorem shifted_criticalPoint (hlim : criticalLimit f κ ∈ hierarchy δ)
    {s t i : V} (hs : s ∈ (ω : V)) (ht : t ∈ (ω : V)) (hi : i ∈ (ω : V))
    (hs0 : s ≠ 0) (ht0 : t ≠ 0) :
    IsCriticalPoint (hierarchy (criticalIterate f κ (ordinalAdd s i)))
      (shiftedCriticalEmbedding δ f κ s t i) (criticalIterate f κ i) := by
  let := hδ.ordinal
  let := hierarchy_transitive δ
  let := (iterate_spec hδ h hκ hs).1
  let := hierarchy_transitive (criticalIterate f κ s)
  let := (iterate_spec hδ h hκ (ordinalAdd_natural hs hi)).1
  have himage : IsTransitive ((embeddingPower (hierarchy δ) f i) ‘ (hierarchy (criticalIterate f κ s))) := by
    rw [power_value_hierarchy hδ h hκ hs hi]
    exact hierarchy_transitive _
  let := himage
  have hA := hδ.hierarchy_closed (iterate_spec hδ h hκ hs).1 (iterate_spec hδ h hκ hs).2.1
  have hB := hδ.hierarchy_closed (iterate_spec hδ h hκ (ordinalAdd_natural hs ht)).1
    (iterate_spec hδ h hκ (ordinalAdd_natural hs ht)).2.1
  have heδ := (hierarchy_transitive δ).mem_trans (power_restriction_mem_limit hδ h hκ hs ht)
    (hδ.hierarchy_closed (limit_ordinal hδ h hκ) hlim)
  have hm := (h.power hi).value_criticalPoint hA hB heδ
    (power_restriction_elementary hδ h hκ hs ht).function
    (power_restriction_criticalPoint hδ h hκ hs ht hs0 ht0)
  rw [power_value_hierarchy hδ h hκ hs hi,
    embeddingPower_value_criticalPoint h hκ.mem_domain hi] at hm
  exact hm

theorem shifted_value_image (hlim : criticalLimit f κ ∈ hierarchy δ)
    {s t i x : V} (hs : s ∈ (ω : V)) (ht : t ∈ (ω : V)) (hi : i ∈ (ω : V))
    (hx : x ∈ hierarchy (criticalIterate f κ s)) :
    (shiftedCriticalEmbedding δ f κ s t i) ‘ ((embeddingPower (hierarchy δ) f i) ‘ x) =
      (embeddingPower (hierarchy δ) f i) ‘ ((embeddingPower (hierarchy δ) f t) ‘ x) := by
  let := hδ.ordinal
  let := hierarchy_transitive δ
  have he := power_restriction_elementary hδ h hκ hs ht
  have hA := hδ.hierarchy_closed (iterate_spec hδ h hκ hs).1 (iterate_spec hδ h hκ hs).2.1
  have heδ := (hierarchy_transitive δ).mem_trans (power_restriction_mem_limit hδ h hκ hs ht)
    (hδ.hierarchy_closed (limit_ordinal hδ h hκ) hlim)
  have hm := (h.power hi).value_apply heδ hA (IsFunction.of_mem he.function)
    (domain_eq_of_mem_function he.function) hx
  rw [power_restriction_value hδ h hκ hs ht hx] at hm
  exact hm

theorem shifted_value_criticalPoint (hlim : criticalLimit f κ ∈ hierarchy δ)
    {s t i : V} (hs : s ∈ (ω : V)) (ht : t ∈ (ω : V)) (hi : i ∈ (ω : V)) (hs0 : s ≠ 0) :
    (shiftedCriticalEmbedding δ f κ s t i) ‘ (criticalIterate f κ i) =
      criticalIterate f κ (ordinalAdd t i) := by
  let := (iterate_spec hδ h hκ hs).1
  have hκs := ordinal_subset_hierarchy _ κ (criticalPoint_lt_iterate hδ h hκ hs hs0)
  have he := shifted_value_image hδ h hκ hlim hs ht hi hκs
  rw [embeddingPower_value_criticalPoint h hκ.mem_domain hi,
    embeddingPower_value_criticalPoint h hκ.mem_domain ht,
    embeddingPower_value_criticalIterate h hκ.mem_domain ht hi] at he
  exact he

theorem shifted_value_criticalIterate (hlim : criticalLimit f κ ∈ hierarchy δ)
    {s t i p : V} (hs : s ∈ (ω : V)) (ht : t ∈ (ω : V)) (hi : i ∈ (ω : V))
    (hp : p ∈ (ω : V)) (hps : criticalIterate f κ p ∈ criticalIterate f κ s) :
    (shiftedCriticalEmbedding δ f κ s t i) ‘ (criticalIterate f κ (ordinalAdd p i)) =
      criticalIterate f κ (ordinalAdd (ordinalAdd p t) i) := by
  let := (iterate_spec hδ h hκ hs).1
  have hx := ordinal_subset_hierarchy _ _ hps
  have he := shifted_value_image hδ h hκ hlim hs ht hi hx
  rw [embeddingPower_value_criticalIterate h hκ.mem_domain hp hi,
    embeddingPower_value_criticalIterate h hκ.mem_domain hp ht,
    embeddingPower_value_criticalIterate h hκ.mem_domain (ordinalAdd_natural hp ht) hi] at he
  exact he

end CriticalSequence

end ZFVP
