import ZFVP.ModelTheory.WoodinSparseInverseValues
import ZFVP.ModelTheory.WoodinRecodedInverseCoherence
import ZFVP.ModelTheory.WoodinSparseDirectBase

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
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
local notation "N" => woodinNormalizedPrefixCode θ
local notation "C" => woodinNormalizedStageCode θ
local notation "f" => woodinSparseInverseBaseMap θ c m

include hΩ hAC hθ h0 hlim hn hm hT hQt hTt hsp hπ ht hQrank

theorem woodinSparseCompletedInverseMap_projection {i z : V} (hi : i ∈ θ)
    (hz : z ∈ (forcingCodeP C) ‘ θ) :
    ((woodinSparseCompletedInverseMap θ c m) ‘ z) ↾ (succ (woodinSourceIndex i)) =
      (m ‘ i) ‘ (((forcingCodeπ C) ‘ ⟨i, θ⟩ₖ) ‘ z) := by
  let := hΩ.inaccessible.1
  have hsub := IsOrdinal.toIsTransitive.transitive _ hθ
  have hzero : (∅ : V) ∈ θ := (IsOrdinal.subset_iff.mp (empty_subset θ)).resolve_left (fun he ↦ h0 he.symm)
  have hl := ordinal_limit_of_not_successor hlim
  have hb : succ (woodinSourceIndex i) ⊆ θ := by
    simpa only [woodinSparseBounds_value hi] using woodinSparseBounds_limit_subset hzero hl hi
  have hp : kpair.π₁ z ∈ woodinNormalizedInverseBase θ := by
    rw [(woodinNormalized_inverse_dictionary hΩ hAC hθ h0 hlim hn).1] at hz
    obtain ⟨p, hp, τ, _, rfl⟩ := mem_prod_iff.mp hz
    simpa only [kpair.π₁_kpair] using hp
  rw [← restrict_restrict_of_subset hb,
    woodinSparseCompletedInverseMap_restrict hΩ hAC hθ h0 hlim hn hm hT hQt hTt hsp hπ ht hQrank hz,
    woodinSparseInverseBaseMap_restrict hΩ hAC hsub hm hT hQt hTt hzero hl hsp hπ hp hi,
    woodinNormalizedStage_inverse_projection hΩ hAC hθ h0 hlim hn hi hz]

theorem woodinSparseCompletedInverseMap_empty_tail {p : V}
    (hp : ⟨p, ∅⟩ₖ ∈ (forcingCodeP C) ‘ θ) :
    (woodinSparseCompletedInverseMap θ c m) ‘ ⟨p, ∅⟩ₖ = f ‘ p := by
  let := hΩ.inaccessible.1
  have hsub := IsOrdinal.toIsTransitive.transitive _ hθ
  have hzero : (∅ : V) ∈ θ := (IsOrdinal.subset_iff.mp (empty_subset θ)).resolve_left (fun he ↦ h0 he.symm)
  have hl := ordinal_limit_of_not_successor hlim
  have hb := woodinSparseInverseBase_recoded_laws hΩ hAC hsub hm hT hQt hTt hzero hl hsp hπ ht
  rw [woodinSparseCompletedInverseMap_value hΩ hAC hθ h0 hlim hn hm hT hQt hTt hsp hπ ht hQrank hp]
  simp only [kpair.π₁_kpair, kpair.π₂_kpair, normalizedIsomorphismName_empty hb.1 hb.2.1, sparseAppend_empty]

theorem woodinSparseCompletedInverseMap_top :
    (woodinSparseCompletedInverseMap θ c m) ‘ ((forcingCodet C) ‘ θ) = ∅ := by
  let := hΩ.inaccessible.1
  have hsub := IsOrdinal.toIsTransitive.transitive _ hθ
  have hzero : (∅ : V) ∈ θ := (IsOrdinal.subset_iff.mp (empty_subset θ)).resolve_left (fun he ↦ h0 he.symm)
  have hl := ordinal_limit_of_not_successor hlim
  have hp := ((woodinNormalizedStageCode_valid hΩ hAC hθ).system.tops.top θ (mem_succ_self θ)).1
  rw [woodinNormalizedStage_inverse_top h0 hlim hn] at hp ⊢
  rw [woodinSparseCompletedInverseMap_empty_tail hΩ hAC hθ h0 hlim hn hm hT hQt hTt hsp hπ ht hQrank hp]
  exact woodinSparseInverseBaseMap_top hΩ hAC hsub hm hT hQt hTt hzero hl hsp hπ ht

theorem woodinSparseCompletedInverseMap_section {i p : V} (hi : i ∈ θ) (hp : p ∈ (forcingCodeP N) ‘ i)
    (hE : ∀ i ∈ θ, ∀ j ∈ θ, i ⊆ j → ∀ p ∈ Q ‘ i,
      ((forcingRecodedSections θ N m) ‘ ⟨i, j⟩ₖ) ‘ p = p) :
    (woodinSparseCompletedInverseMap θ c m) ‘ (((forcingCodeE C) ‘ ⟨i, θ⟩ₖ) ‘ p) = (m ‘ i) ‘ p := by
  let := hΩ.inaccessible.1
  have hsub := IsOrdinal.toIsTransitive.transitive _ hθ
  have hzero : (∅ : V) ∈ θ := (IsOrdinal.subset_iff.mp (empty_subset θ)).resolve_left (fun he ↦ h0 he.symm)
  have hl := ordinal_limit_of_not_successor hlim
  have hs := woodinNormalizedPrefixCode_valid hΩ hAC hsub
  have hc := forcingRecoded_code hs hm hT hQt hTt
  have hpC : p ∈ (forcingCodeP C) ‘ i := (woodinNormalizedStage_inverse_old_carrier h0 hlim hn hi).symm ▸ hp
  have hz := (woodinNormalizedStageCode_valid hΩ hAC hθ).system.split.secMaps
    i (mem_succ_iff.mpr (Or.inr hi)) θ (mem_succ_self θ) (IsOrdinal.toIsTransitive.transitive _ hi) p hpC
  rw [woodinNormalizedStage_inverse_section_normalized hΩ hAC hθ h0 hlim hn hi hp] at hz ⊢
  rw [woodinSparseCompletedInverseMap_empty_tail hΩ hAC hθ h0 hlim hn hm hT hQt hTt hsp hπ ht hQrank hz]
  have hsrc : forcingSectionThread θ (forcingCodeπ N) (forcingCodeE N) i p ∈ woodinNormalizedInverseBase θ :=
    forcingDirectLimit_subset _ _ _ _ _ _
      (forcingSectionThread_mem hs.system.split hi hp (woodinNormalizedPrefix_subset_universe hΩ hAC hsub))
  rw [woodinSparseInverseBaseMap_value hΩ hAC hsub hm hT hQt hTt hzero hl hsp hπ hsrc,
    forcingRecoded_sectionThread hs hm hi hp]
  have hq : (m ‘ i) ‘ p ∈ (forcingCodeP c) ‘ i := by
    simpa only [forcingRecodedCode, forcingCodeP_code] using function_value_mem (hm i hi).1 hp
  have hraw : forcingSectionThread θ (forcingCodeπ c) (forcingCodeE c) i ((m ‘ i) ‘ p) ∈
      forcingInverseCodePoset θ c := forcingDirectLimit_subset _ _ _ _ _ _
        (forcingSectionThread_mem hc.system.split hi hq hc.subset_universe)
  have hπ' : ∀ i ∈ θ, ∀ j ∈ θ, i ∈ j → ∀ p ∈ (forcingCodeP c) ‘ j,
      ((forcingCodeπ c) ‘ ⟨i, j⟩ₖ) ‘ p = p ↾ (succ (woodinSourceIndex i)) := by
    simpa only [forcingRecodedCode, forcingCodeP_code, forcingCodeπ_code] using hπ
  have hE' : ∀ i ∈ θ, ∀ j ∈ θ, i ⊆ j → ∀ p ∈ (forcingCodeP c) ‘ i,
      ((forcingCodeE c) ‘ ⟨i, j⟩ₖ) ‘ p = p := by
    simpa only [forcingRecodedCode, forcingCodeP_code, forcingCodeE_code] using hE
  have he := woodinSparseDirect_union_of_support hπ' hE' hraw (forcingSectionThread_support hc.system.split hi hq)
  rw [forcingSectionThread_value hi, forcingSectionValue_self hc.system.split hi hq] at he
  simpa only [forcingRecodedCode, forcingCodeπ_code, forcingCodeE_code] using he

end ZFVP
