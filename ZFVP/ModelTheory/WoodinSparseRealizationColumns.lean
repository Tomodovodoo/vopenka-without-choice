import ZFVP.ModelTheory.WoodinSparseRealization

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable {Ω θ : V} [IsOrdinal θ]
local notation "A" => kpair.π₁ (woodinIterationRec θ)
local notation "N" => woodinNormalizedStageCode θ
local notation "C" => woodinSparseStageCode θ

theorem woodinIterationStage_old_row
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω)
    {i : V} (hi : i ∈ θ) :
    (forcingCodeP A) ‘ i = (forcingCodeP (kpair.π₁ (woodinIterationRec i))) ‘ i ∧
    (forcingCodeR A) ‘ i = (forcingCodeR (kpair.π₁ (woodinIterationRec i))) ‘ i := by
  let := IsOrdinal.of_mem hi
  have hh := woodinIterationHistory_of_stages
    (fun j hj ↦ ((woodinIterationExit hΩ hAC).2.1 j (hθ j hj)).1)
  have he := (woodinIterationRec_extends_previous hh hi).1
  have hs := ((woodinIterationExit hΩ hAC).2.1 i (hθ i hi)).1.code
  have ht := woodinIterationStageCode_valid_le hΩ hAC hθ
  exact ⟨(hs.tableP.value_of_subset ht.tableP he.subP (mem_succ_self i)).symm,
    (hs.tableR.value_of_subset ht.tableR he.subR (mem_succ_self i)).symm⟩

theorem woodinSparseRealizationMap_top
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω) :
    (woodinSparseRealizationMap θ) ‘ ((forcingCodet A) ‘ θ) = ∅ := by
  have ht := ((woodinIterationStageCode_valid_le hΩ hAC hθ).system.tops.top θ (mem_succ_self θ)).1
  have hfix := (woodinNormalizationHistory_family_le hΩ hAC hθ).fixesTop θ (mem_succ_self θ)
  rw [woodinNormalizationHistory_value (mem_succ_self θ)] at hfix
  rw [woodinSparseRealizationMap_value hΩ hAC hθ ht, hfix]
  have he := (woodinSparseRecodingRec_correct_le hΩ hAC hθ).2.2.1
  simpa only [woodinSparseStageMap, woodinNormalizedStageCode, forcingNormalizedCode, forcingCodet_code] using he

theorem woodinIterationStage_old_top
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω)
    {i : V} (hi : i ∈ θ) :
    (forcingCodet A) ‘ i = (forcingCodet (kpair.π₁ (woodinIterationRec i))) ‘ i := by
  let := IsOrdinal.of_mem hi
  have hh := woodinIterationHistory_of_stages
    (fun j hj ↦ ((woodinIterationExit hΩ hAC).2.1 j (hθ j hj)).1)
  have he := (woodinIterationRec_extends_previous hh hi).1
  have hs := ((woodinIterationExit hΩ hAC).2.1 i (hθ i hi)).1.code
  have ht := woodinIterationStageCode_valid_le hΩ hAC hθ
  exact (hs.tablet.value_of_subset ht.tablet he.subt (mem_succ_self i)).symm

theorem woodinSparseRealizationMap_restrict
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω)
    {i p : V} (hi : i ∈ θ) (hp : p ∈ (forcingCodeP A) ‘ θ) :
    ((woodinSparseRealizationMap θ) ‘ p) ↾ (succ (woodinSourceIndex i)) =
      (woodinSparseRealizationMap i) ‘ (((forcingCodeπ A) ‘ ⟨i, θ⟩ₖ) ‘ p) := by
  let := hΩ.inaccessible.1
  let := IsOrdinal.of_mem hi
  have hisub := IsOrdinal.toIsTransitive.transitive _ (hθ i hi)
  have hn := woodinNormalizationHistory_family_le hΩ hAC hθ
  have hs := woodinIterationStageCode_valid_le hΩ hAC hθ
  have hr := woodinNormalizationRec_retraction_le hΩ hAC hθ
  have hnp := function_value_mem hr.maps hp
  have ht := mem_succ_self θ
  have hi' : i ∈ succ θ := mem_succ_iff.mpr (Or.inr hi)
  have hip : ((forcingCodeπ A) ‘ ⟨i, θ⟩ₖ) ‘ p ∈ (forcingCodeP (kpair.π₁ (woodinIterationRec i))) ‘ i := by
    rw [← (woodinIterationStage_old_row hΩ hAC hθ hi).1]
    exact hs.system.split.projMaps i hi' θ ht (IsOrdinal.toIsTransitive.transitive _ hi) p hp
  have hnorm := hn.projection θ ht i hi hi' p hp
  simp only [woodinNormalizationHistory_value ht, woodinNormalizationHistory_value hi'] at hnorm
  have happly := forcingNormalizationProjections_apply hn hs hi' ht
    (IsOrdinal.toIsTransitive.transitive _ hi)
    (show (woodinNormalizationRec θ) ‘ p ∈
      (forcingNormalizationCarriers (succ θ) A (woodinNormalizationHistory (succ θ))) ‘ θ by
        simpa only [woodinNormalizedStageCode, forcingNormalizedCode, forcingCodeP_code] using hnp)
  have hrow := (woodinSparseRecodingRec_correct_le hΩ hAC hθ).2.2.2.1 i hi _ hnp
  change ((woodinSparseStageMap θ) ‘ ((woodinNormalizationRec θ) ‘ p)) ↾ (succ (woodinSourceIndex i)) =
    (woodinSparseStageMap i) ‘ (((forcingCodeπ N) ‘ ⟨i, θ⟩ₖ) ‘ ((woodinNormalizationRec θ) ‘ p)) at hrow
  rw [woodinSparseRealizationMap_value hΩ hAC hθ hp, woodinSparseRealizationMap_value hΩ hAC hisub hip, hrow]
  apply congrArg (fun q : V ↦ (woodinSparseStageMap i) ‘ q)
  simpa only [woodinNormalizedStageCode, forcingNormalizedCode, forcingCodeπ_code] using happly.trans hnorm

end ZFVP
