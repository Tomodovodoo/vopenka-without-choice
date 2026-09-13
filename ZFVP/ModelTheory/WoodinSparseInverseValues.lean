import ZFVP.ModelTheory.WoodinSparseInverseIsomorphism

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem woodinSparseInversePairMap_value {Ω θ c m z : V} [IsOrdinal θ]
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ∈ Ω)
    (h0 : θ ≠ ∅) (hlim : θ ≠ succ (⋃ˢ θ))
    (hn : ¬IsChoicelessInaccessible (woodinLimitCardinal (woodinIterationCardinalPrefix θ)))
    (hz : z ∈ (forcingCodeP (woodinNormalizedStageCode θ)) ‘ θ) :
    (woodinSparseInversePairMap θ c m) ‘ z =
      normalizedTwoStepIsoValue (woodinSparseInverseBase θ c) (woodinSparseInverseOrder θ c) ∅
        (woodinSparseInverseBaseMap θ c m) z := by
  rw [(woodinNormalized_inverse_dictionary hΩ hAC hθ h0 hlim hn).1] at hz
  rw [woodinSparseInversePairMap, woodinNormalizedInverseCutoff, normalizedTwoStepIsoMap_value hz]

variable {Ω θ Q T m : V} [IsOrdinal θ]
variable (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ∈ Ω)
variable (h0 : θ ≠ ∅) (hlim : θ ≠ succ (⋃ˢ θ))
variable (hn : ¬IsChoicelessInaccessible (woodinLimitCardinal (woodinIterationCardinalPrefix θ)))
variable (hm : ∀ i ∈ θ, IsForcingIsomorphism ((forcingCodeP (woodinNormalizedPrefixCode θ)) ‘ i)
  ((forcingCodeR (woodinNormalizedPrefixCode θ)) ‘ i) (Q ‘ i) (T ‘ i) (m ‘ i))
variable (hT : ∀ i ∈ θ, IsForcingPreorder (Q ‘ i) (T ‘ i))
variable (hQt : IsIterationTable θ Q) (hTt : IsIterationTable θ T)
variable (hsp : ∀ i ∈ θ, ∀ p ∈ Q ‘ i, IsSparseFunctionOn (succ (woodinSourceIndex i)) p)
variable (hπ : ∀ i ∈ θ, ∀ j ∈ θ, i ∈ j → ∀ p ∈ Q ‘ j,
  ((forcingRecodedProjections θ (woodinNormalizedPrefixCode θ) m) ‘ ⟨i, j⟩ₖ) ‘ p =
    p ↾ (succ (woodinSourceIndex i)))
variable (ht : ∀ i ∈ θ, (forcingRecodedTops θ (woodinNormalizedPrefixCode θ) m) ‘ i = ∅)
variable (hQrank : ∀ i ∈ θ, Q ‘ i ∈ hierarchy (woodinNormalizedInverseCutoff θ))

local notation "c" => forcingRecodedCode θ (woodinNormalizedPrefixCode θ) Q T m
local notation "A" => woodinSparseInverseBase θ c
local notation "B" => woodinSparseInverseOrder θ c
local notation "f" => woodinSparseInverseBaseMap θ c m

include hΩ hAC hθ h0 hlim hn hm hT hQt hTt hsp hπ ht hQrank

theorem woodinSparseCompletedInverseMap_value {z : V}
    (hz : z ∈ (forcingCodeP (woodinNormalizedStageCode θ)) ‘ θ) :
    (woodinSparseCompletedInverseMap θ c m) ‘ z =
      sparseAppend θ (f ‘ (kpair.π₁ z)) (normalizedIsomorphismName A B ∅ f (kpair.π₂ z)) := by
  have hf := woodinSparseInversePairMap_isomorphism hΩ hAC hm hT hQt hTt hsp hπ ht hθ h0 hlim hn hQrank
  have he := woodinSparseInverseEncode_isomorphism (θ := θ) («c» := c)
  have hA : ∀ p ∈ A, IsSparseFunctionOn θ p := fun _ hp ↦ sparseThreadCarrier_isSparse hp
  rw [woodinSparseCompletedInverseMap, value_compose_of_mem_function hf.1 he.1 hz,
    sparsePairEncode_value_of_mem (W := woodinSparseInversePool θ c) hA (function_value_mem hf.1 hz),
    woodinSparseInversePairMap_value hΩ hAC hθ h0 hlim hn hz]
  simp only [normalizedTwoStepIsoValue, kpair.π₁_kpair, kpair.π₂_kpair]

theorem woodinSparseCompletedInverseMap_base_mem {z : V}
    (hz : z ∈ (forcingCodeP (woodinNormalizedStageCode θ)) ‘ θ) : f ‘ (kpair.π₁ z) ∈ A := by
  have hf := woodinSparseInversePairMap_isomorphism hΩ hAC hm hT hQt hTt hsp hπ ht hθ h0 hlim hn hQrank
  have hmem := function_value_mem hf.1 hz
  rw [woodinSparseInversePairMap_value hΩ hAC hθ h0 hlim hn hz] at hmem
  exact (kpair_mem_iff.mp hmem).1

theorem woodinSparseCompletedInverseMap_restrict {z : V}
    (hz : z ∈ (forcingCodeP (woodinNormalizedStageCode θ)) ‘ θ) :
    ((woodinSparseCompletedInverseMap θ c m) ‘ z) ↾ θ = f ‘ (kpair.π₁ z) := by
  have hs := sparseThreadCarrier_isSparse
    (woodinSparseCompletedInverseMap_base_mem hΩ hAC hθ h0 hlim hn hm hT hQt hTt hsp hπ ht hQrank hz)
  let := hs.1
  rw [woodinSparseCompletedInverseMap_value hΩ hAC hθ h0 hlim hn hm hT hQt hTt hsp hπ ht hQrank hz]
  exact sparseAppend_restrict hs.2.1

theorem woodinSparseCompletedInverseMap_tail {z : V}
    (hz : z ∈ (forcingCodeP (woodinNormalizedStageCode θ)) ‘ θ) :
    ((woodinSparseCompletedInverseMap θ c m) ‘ z) ‘ θ = normalizedIsomorphismName A B ∅ f (kpair.π₂ z) := by
  have hs := sparseThreadCarrier_isSparse
    (woodinSparseCompletedInverseMap_base_mem hΩ hAC hθ h0 hlim hn hm hT hQt hTt hsp hπ ht hQrank hz)
  let := hs.1
  rw [woodinSparseCompletedInverseMap_value hΩ hAC hθ h0 hlim hn hm hT hQt hTt hsp hπ ht hQrank hz]
  exact sparseAppend_value_new hs.2.1

end ZFVP
