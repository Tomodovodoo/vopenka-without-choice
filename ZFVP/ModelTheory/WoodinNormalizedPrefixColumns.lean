import ZFVP.ModelTheory.WoodinRecodingHistory

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable {Ω θ i j : V} [IsOrdinal θ]
variable (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω) (hj : j ∈ θ)
local notation "N" => woodinNormalizedPrefixCode θ
local notation "C" => woodinNormalizedStageCode j
include hΩ hAC hθ hj

theorem woodinNormalizedPrefix_extends_stage : ForcingCodeExtends C N := by
  let := IsOrdinal.of_mem hj
  have hsub : succ j ⊆ θ := by
    intro k hk
    rcases mem_succ_iff.mp hk with rfl | hk
    · exact hj
    · exact IsOrdinal.toIsTransitive.mem_trans hk hj
  have he := woodinNormalizedPrefix_extends hΩ hAC hθ hsub
  rwa [woodinNormalizedPrefix_successor hΩ hAC (hθ j hj)] at he

theorem woodinNormalizedPrefix_stage_carrier (hi : i ∈ succ j) :
    (forcingCodeP N) ‘ i = (forcingCodeP C) ‘ i := by
  let := IsOrdinal.of_mem hj
  exact ((woodinNormalizedStageCode_valid hΩ hAC (hθ j hj)).tableP.value_of_subset
    (woodinNormalizedPrefixCode_valid hΩ hAC hθ).tableP
    (woodinNormalizedPrefix_extends_stage hΩ hAC hθ hj).subP hi).symm

theorem woodinNormalizedPrefix_stage_order (hi : i ∈ succ j) :
    (forcingCodeR N) ‘ i = (forcingCodeR C) ‘ i := by
  let := IsOrdinal.of_mem hj
  exact ((woodinNormalizedStageCode_valid hΩ hAC (hθ j hj)).tableR.value_of_subset
    (woodinNormalizedPrefixCode_valid hΩ hAC hθ).tableR
    (woodinNormalizedPrefix_extends_stage hΩ hAC hθ hj).subR hi).symm

theorem woodinNormalizedPrefix_stage_projection (hi : i ∈ succ j) :
    (forcingCodeπ N) ‘ ⟨i, j⟩ₖ = (forcingCodeπ C) ‘ ⟨i, j⟩ₖ := by
  let := IsOrdinal.of_mem hj
  exact ((woodinNormalizedStageCode_valid hΩ hAC (hθ j hj)).tableπ.value_of_subset
    (woodinNormalizedPrefixCode_valid hΩ hAC hθ).tableπ
    (woodinNormalizedPrefix_extends_stage hΩ hAC hθ hj).subπ
    (kpair_mem_iff.mpr ⟨hi, mem_succ_self j⟩)).symm

theorem woodinNormalizedPrefix_stage_section (hi : i ∈ succ j) :
    (forcingCodeE N) ‘ ⟨i, j⟩ₖ = (forcingCodeE C) ‘ ⟨i, j⟩ₖ := by
  let := IsOrdinal.of_mem hj
  exact ((woodinNormalizedStageCode_valid hΩ hAC (hθ j hj)).tableE.value_of_subset
    (woodinNormalizedPrefixCode_valid hΩ hAC hθ).tableE
    (woodinNormalizedPrefix_extends_stage hΩ hAC hθ hj).subE
    (kpair_mem_iff.mpr ⟨hi, mem_succ_self j⟩)).symm

theorem woodinNormalizedPrefix_stage_lift (hi : i ∈ succ j) :
    (forcingCodeL N) ‘ ⟨i, j⟩ₖ = (forcingCodeL C) ‘ ⟨i, j⟩ₖ := by
  let := IsOrdinal.of_mem hj
  exact ((woodinNormalizedStageCode_valid hΩ hAC (hθ j hj)).tableL.value_of_subset
    (woodinNormalizedPrefixCode_valid hΩ hAC hθ).tableL
    (woodinNormalizedPrefix_extends_stage hΩ hAC hθ hj).subL
    (kpair_mem_iff.mpr ⟨hi, mem_succ_self j⟩)).symm

theorem woodinNormalizedPrefix_stage_top :
    (forcingCodet N) ‘ j = (forcingCodet C) ‘ j := by
  let := IsOrdinal.of_mem hj
  exact ((woodinNormalizedStageCode_valid hΩ hAC (hθ j hj)).tablet.value_of_subset
    (woodinNormalizedPrefixCode_valid hΩ hAC hθ).tablet
    (woodinNormalizedPrefix_extends_stage hΩ hAC hθ hj).subt (mem_succ_self j)).symm

end ZFVP
