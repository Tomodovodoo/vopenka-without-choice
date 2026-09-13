import ZFVP.ModelTheory.WoodinActualInverseMaps
import ZFVP.SetTheory.ForcingCodeExtensionValues

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable {θ s K m i j : V}
local notation "C" => forcingNormalizedCode (succ θ) (woodinInverseSourceCode θ s K)
  (woodinNormalizationInverse θ s K m)
local notation "D" => forcingNormalizedCode θ s m

theorem woodinNormalizedInverse_old_projection (hi : i ∈ θ) (hj : j ∈ θ) :
    (forcingCodeπ C) ‘ ⟨i, j⟩ₖ = (forcingCodeπ D) ‘ ⟨i, j⟩ₖ := by
  have hi' := mem_succ_iff.mpr (Or.inr hi)
  have hj' := mem_succ_iff.mpr (Or.inr hj)
  simp only [forcingNormalizedCode, forcingCodeπ_code,
    forcingNormalizationProjections_value hi hj, forcingNormalizationProjections_value hi' hj',
    forcingNormalizationCarriers_value hj, forcingNormalizationCarriers_value hj',
    woodinNormalizationInverse_old hj, woodinInverseSourceCode_twoStepColumn,
    forcingTwoStepColumnCode, forcingIterationCodeNext, forcingCodeπ_code, forcingCodeP_code,
    forcingMatrixNext_old hi' hj, forcingFamilyNext_old hj]

theorem woodinNormalizedInverse_old_section (hi : i ∈ θ) (hj : j ∈ θ) :
    (forcingCodeE C) ‘ ⟨i, j⟩ₖ = (forcingCodeE D) ‘ ⟨i, j⟩ₖ := by
  have hi' := mem_succ_iff.mpr (Or.inr hi)
  have hj' := mem_succ_iff.mpr (Or.inr hj)
  simp only [forcingNormalizedCode, forcingCodeE_code,
    forcingNormalizationSections_value hi hj, forcingNormalizationSections_value hi' hj',
    forcingNormalizationCarriers_value hi, forcingNormalizationCarriers_value hi',
    woodinNormalizationInverse_old hi, woodinInverseSourceCode_twoStepColumn,
    forcingTwoStepColumnCode, forcingIterationCodeNext, forcingCodeE_code, forcingCodeP_code,
    forcingMatrixNext_old hi' hj, forcingFamilyNext_old hi]

theorem woodinNormalizedInverse_old_lift (hi : i ∈ θ) (hj : j ∈ θ) :
    (forcingCodeL C) ‘ ⟨i, j⟩ₖ = (forcingCodeL D) ‘ ⟨i, j⟩ₖ := by
  have hi' := mem_succ_iff.mpr (Or.inr hi)
  have hj' := mem_succ_iff.mpr (Or.inr hj)
  simp only [forcingNormalizedCode, forcingCodeL_code,
    forcingNormalizationLifts_value hi hj, forcingNormalizationLifts_value hi' hj',
    forcingNormalizationCarriers_value hi, forcingNormalizationCarriers_value hi',
    forcingNormalizationCarriers_value hj, forcingNormalizationCarriers_value hj',
    woodinNormalizationInverse_old hi, woodinNormalizationInverse_old hj, woodinInverseSourceCode_twoStepColumn,
    forcingTwoStepColumnCode, forcingIterationCodeNext, forcingCodeL_code, forcingCodeP_code,
    forcingMatrixNext_old hi' hj, forcingFamilyNext_old hi, forcingFamilyNext_old hj]

theorem woodinNormalizedInverse_old_top (hi : i ∈ θ) : (forcingCodet C) ‘ i = (forcingCodet D) ‘ i := by
  simp only [forcingNormalizedCode, forcingCodet_code, woodinInverseSourceCode_twoStepColumn,
    forcingTwoStepColumnCode, forcingIterationCodeNext, forcingCodet_code, forcingFamilyNext_old hi]

variable [IsOrdinal θ]
local notation "N" => woodinNormalizedPrefixCode θ
local notation "S" => woodinNormalizedStageCode θ
local notation "γ" => woodinLimitCardinal (woodinIterationCardinalPrefix θ)

theorem woodinNormalizedStage_inverse_old_maps
    (h0 : θ ≠ ∅) (hlim : θ ≠ succ (⋃ˢ θ)) (hn : ¬IsChoicelessInaccessible γ)
    (hi : i ∈ θ) (hj : j ∈ θ) :
    (forcingCodeπ S) ‘ ⟨i, j⟩ₖ = (forcingCodeπ N) ‘ ⟨i, j⟩ₖ ∧
    (forcingCodeE S) ‘ ⟨i, j⟩ₖ = (forcingCodeE N) ‘ ⟨i, j⟩ₖ ∧
    (forcingCodeL S) ‘ ⟨i, j⟩ₖ = (forcingCodeL N) ‘ ⟨i, j⟩ₖ := by
  rw [woodinNormalizedStage_inverse_code h0 hlim hn]
  exact ⟨woodinNormalizedInverse_old_projection hi hj, woodinNormalizedInverse_old_section hi hj,
    woodinNormalizedInverse_old_lift hi hj⟩

theorem woodinNormalizedStage_inverse_old_top
    (h0 : θ ≠ ∅) (hlim : θ ≠ succ (⋃ˢ θ)) (hn : ¬IsChoicelessInaccessible γ) (hi : i ∈ θ) :
    (forcingCodet S) ‘ i = (forcingCodet N) ‘ i := by
  rw [woodinNormalizedStage_inverse_code h0 hlim hn]
  exact woodinNormalizedInverse_old_top hi

theorem woodinNormalizedStage_inverse_extends {Ω : V}
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ∈ Ω)
    (h0 : θ ≠ ∅) (hlim : θ ≠ succ (⋃ˢ θ)) (hn : ¬IsChoicelessInaccessible γ) :
    ForcingCodeExtends N S := by
  let := hΩ.inaccessible.1
  have hsub := IsOrdinal.toIsTransitive.transitive _ hθ
  apply ForcingCodeExtends.of_values (woodinNormalizedPrefixCode_valid hΩ hAC hsub)
    (woodinNormalizedStageCode_valid hΩ hAC hθ) (fun _ hi ↦ mem_succ_iff.mpr (Or.inr hi))
  · exact fun _ hi ↦ (woodinNormalizedStage_inverse_old_carrier h0 hlim hn hi).symm
  · exact fun _ hi ↦ (woodinNormalizedStage_inverse_old_order h0 hlim hn hi).symm
  · exact fun _ hi _ hj ↦ (woodinNormalizedStage_inverse_old_maps h0 hlim hn hi hj).1.symm
  · exact fun _ hi _ hj ↦ (woodinNormalizedStage_inverse_old_maps h0 hlim hn hi hj).2.1.symm
  · exact fun _ hi _ hj ↦ (woodinNormalizedStage_inverse_old_maps h0 hlim hn hi hj).2.2.symm
  · exact fun _ hi ↦ (woodinNormalizedStage_inverse_old_top h0 hlim hn hi).symm

end ZFVP
