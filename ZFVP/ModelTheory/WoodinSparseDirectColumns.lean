import ZFVP.ModelTheory.WoodinSparseDirectTransport
import ZFVP.ModelTheory.WoodinActualDirectMaps
import ZFVP.ModelTheory.ForcingSectionThreadTransport
import ZFVP.ModelTheory.WoodinNormalizedEndpoint
namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable {Ω θ Q T m : V} [IsOrdinal θ]
variable (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω)
variable (hm : ∀ i ∈ θ, IsForcingIsomorphism ((forcingCodeP (woodinNormalizedPrefixCode θ)) ‘ i)
  ((forcingCodeR (woodinNormalizedPrefixCode θ)) ‘ i) (Q ‘ i) (T ‘ i) (m ‘ i))
variable (hT : ∀ i ∈ θ, IsForcingPreorder (Q ‘ i) (T ‘ i))
variable (hQt : IsIterationTable θ Q) (hTt : IsIterationTable θ T)
variable (h0 : θ ≠ ∅) (hlim : θ ≠ succ (⋃ˢ θ))
variable (hsp : ∀ i ∈ θ, ∀ p ∈ Q ‘ i, IsSparseFunctionOn (succ (woodinSourceIndex i)) p)
variable (hπ : ∀ i ∈ θ, ∀ j ∈ θ, i ∈ j → ∀ p ∈ Q ‘ j,
  ((forcingRecodedProjections θ (woodinNormalizedPrefixCode θ) m) ‘ ⟨i, j⟩ₖ) ‘ p =
    p ↾ (succ (woodinSourceIndex i)))
variable (hE : ∀ i ∈ θ, ∀ j ∈ θ, i ⊆ j → ∀ p ∈ Q ‘ i,
  ((forcingRecodedSections θ (woodinNormalizedPrefixCode θ) m) ‘ ⟨i, j⟩ₖ) ‘ p = p)

local notation "N" => woodinNormalizedPrefixCode θ
local notation "C" => woodinNormalizedStageCode θ
local notation "S" => woodinIterationPrefix θ
local notation "M" => woodinNormalizationHistory θ
local notation "c" => forcingRecodedCode θ N Q T m
variable (hinac : IsChoicelessInaccessible (woodinLimitCardinal (woodinIterationCardinalPrefix θ)))
include hΩ hAC hθ h0 hlim hinac in
theorem woodinNormalizedStage_direct_section_normalized {i p : V}
    (hi : i ∈ θ) (hp : p ∈ (forcingCodeP N) ‘ i) :
    ((forcingCodeE C) ‘ ⟨i, θ⟩ₖ) ‘ p = forcingSectionThread θ (forcingCodeπ N) (forcingCodeE N) i p := by
  let := hΩ.inaccessible.1
  have hs := woodinIterationPrefix_of_stages
    (fun j hj ↦ ((woodinIterationExit hΩ hAC).2.1 j (hθ j hj)).1)
  have hn := woodinNormalizationHistory_actual_prefix hΩ hAC hθ
  have hfamily : IsForcingNormalizationFamily (succ θ) (kpair.π₁ (woodinIterationRec θ))
      (woodinNormalizationHistory (succ θ)) := by
    rcases IsOrdinal.subset_iff.mp hθ with rfl | hθ
    · exact woodinNormalizationHistory_endpoint_family hΩ hAC
    · exact woodinNormalizationHistory_family hΩ hAC θ hθ
  have hcode : IsForcingIterationCode (succ θ) (kpair.π₁ (woodinIterationRec θ)) := by
    rcases IsOrdinal.subset_iff.mp hθ with rfl | hθ
    · exact (woodinIteration_endpoint_valid hΩ hAC).1.code
    · exact ((woodinIterationExit hΩ hAC).2.1 θ hθ).1.code
  have hpN : p ∈ (forcingNormalizationCarriers θ S M) ‘ i := by
    simpa only [woodinNormalizedPrefixCode, forcingNormalizedCode, forcingCodeP_code] using hp
  have hpP := hn.inclusion i hi p hpN
  have hpN' : p ∈ (forcingNormalizationCarriers (succ θ) (kpair.π₁ (woodinIterationRec θ))
      (woodinNormalizationHistory (succ θ))) ‘ i := by
    simpa only [forcingNormalizationCarriers_value hi,
      forcingNormalizationCarriers_value (mem_succ_iff.mpr (Or.inr hi)),
      woodinNormalizationHistory_value hi,
      woodinNormalizationHistory_value (mem_succ_iff.mpr (Or.inr hi)),
      woodinIterationRec_direct h0 hlim hinac, kpair.π₁_kpair,
      forcingDirectCode, forcingThreadCode, forcingIterationCodeNext, forcingCodeP_code,
      forcingFamilyNext_old hi] using hpN
  simp only [woodinNormalizedStageCode, forcingNormalizedCode, forcingCodeE_code]
  rw [forcingNormalizationSections_apply hfamily hcode (mem_succ_iff.mpr (Or.inr hi))
    (mem_succ_self θ) (IsOrdinal.toIsTransitive.transitive _ hi) hpN',
    woodinIterationRec_direct h0 hlim hinac, kpair.π₁_kpair]
  simp only [forcingDirectCode, forcingThreadCode, forcingIterationCodeNext, forcingCodeE_code,
    forcingMatrixNext_column hi, forcingLimitSectionColumn_value hi, forcingThreadSection_value hpP]
  simp only [woodinNormalizedPrefixCode, forcingNormalizedCode, forcingCodeπ_code, forcingCodeE_code]
  exact (forcingNormalized_sectionThread hs.code hn hi hpN).symm

include hΩ hAC hθ hm hT hQt hTt h0 hlim hsp hπ hE hinac in
theorem woodinSparseDirectMap_section {i p : V} (hi : i ∈ θ) (hp : p ∈ (forcingCodeP N) ‘ i) :
    (woodinSparseDirectMap θ c m) ‘ (((forcingCodeE C) ‘ ⟨i, θ⟩ₖ) ‘ p) = (m ‘ i) ‘ p := by
  have hs := woodinNormalizedPrefixCode_valid hΩ hAC hθ
  rw [woodinNormalizedStage_direct_section_normalized hΩ hAC hθ h0 hlim hinac hi hp]
  have hp' : forcingSectionThread θ (forcingCodeπ N) (forcingCodeE N) i p ∈ (forcingCodeP C) ‘ θ := by
    rw [(woodinNormalized_direct_dictionary hΩ hAC hθ h0 hlim hinac).1]
    exact forcingSectionThread_mem hs.system.split hi hp (woodinNormalizedPrefix_subset_universe hΩ hAC hθ)
  rw [woodinSparseDirectMap_of_support hΩ hAC hθ hm hT hQt hTt h0 hlim hsp hπ hE hinac hp'
    (forcingSectionThread_support hs.system.split hi hp), forcingSectionThread_value hi,
    forcingSectionValue_self hs.system.split hi hp]
include hΩ hAC hθ h0 hlim hinac in
theorem woodinNormalizedStage_direct_projection {i p : V}
    (hi : i ∈ θ) (hp : p ∈ (forcingCodeP C) ‘ θ) :
    ((forcingCodeπ C) ‘ ⟨i, θ⟩ₖ) ‘ p = p ‘ i := by
  let := hΩ.inaccessible.1
  have hfamily : IsForcingNormalizationFamily (succ θ) (kpair.π₁ (woodinIterationRec θ))
      (woodinNormalizationHistory (succ θ)) := by
    rcases IsOrdinal.subset_iff.mp hθ with rfl | hθ
    · exact woodinNormalizationHistory_endpoint_family hΩ hAC
    · exact woodinNormalizationHistory_family hΩ hAC θ hθ
  have hcode : IsForcingIterationCode (succ θ) (kpair.π₁ (woodinIterationRec θ)) := by
    rcases IsOrdinal.subset_iff.mp hθ with rfl | hθ
    · exact (woodinIteration_endpoint_valid hΩ hAC).1.code
    · exact ((woodinIterationExit hΩ hAC).2.1 θ hθ).1.code
  have hpN : p ∈ (forcingNormalizationCarriers (succ θ) (kpair.π₁ (woodinIterationRec θ))
      (woodinNormalizationHistory (succ θ))) ‘ θ := by
    simpa only [woodinNormalizedStageCode, forcingNormalizedCode, forcingCodeP_code] using hp
  have hpP := hfamily.inclusion θ (mem_succ_self θ) p hpN
  rw [woodinIterationRec_direct h0 hlim hinac, kpair.π₁_kpair] at hpP
  simp only [forcingDirectCode, forcingThreadCode_poset] at hpP
  simp only [woodinNormalizedStageCode, forcingNormalizedCode, forcingCodeπ_code]
  rw [forcingNormalizationProjections_apply hfamily hcode (mem_succ_iff.mpr (Or.inr hi))
    (mem_succ_self θ) (IsOrdinal.toIsTransitive.transitive _ hi) hpN,
    woodinIterationRec_direct h0 hlim hinac, kpair.π₁_kpair]
  simp only [forcingDirectCode, forcingThreadCode, forcingIterationCodeNext, forcingCodeπ_code,
    forcingMatrixNext_column hi, forcingLimitProjectionColumn_value hi, forcingThreadCoordinate_value hpP]

include hΩ hAC hθ hm hT hQt hTt h0 hlim hsp hπ hE hinac in
theorem woodinSparseDirectMap_projection {i p : V} (hi : i ∈ θ) (hp : p ∈ (forcingCodeP C) ‘ θ) :
    ((woodinSparseDirectMap θ c m) ‘ p) ↾ (succ (woodinSourceIndex i)) =
      (m ‘ i) ‘ (((forcingCodeπ C) ‘ ⟨i, θ⟩ₖ) ‘ p) := by
  rw [woodinNormalizedStage_direct_projection hΩ hAC hθ h0 hlim hinac hi hp]
  exact woodinSparseDirectMap_restrict hΩ hAC hθ hm hT hQt hTt h0 hlim hsp hπ hE hinac hp hi
end ZFVP

