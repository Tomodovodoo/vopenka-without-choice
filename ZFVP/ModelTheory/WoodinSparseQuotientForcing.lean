import ZFVP.ModelTheory.WoodinSparseSourceInvariant
import ZFVP.ModelTheory.EquivalentRetractionQuotientTransfer
import ZFVP.ModelTheory.WoodinSparseCodeCompatibility

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable {Ω θ : V} [IsOrdinal θ]
local notation "A" => kpair.π₁ (woodinIterationRec θ)
local notation "C" => woodinSparseStageCode θ

theorem woodinSparseStageMap_raw_top
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω) :
    (woodinSparseStageMap θ) ‘ ((forcingCodet A) ‘ θ) = ∅ := by
  have ht := ((woodinIterationStageCode_valid_le hΩ hAC hθ).system.tops.top θ (mem_succ_self θ)).1
  have he := (woodinNormalizationRec_retraction_le hΩ hAC hθ).fixes _ (woodinNormalizedStage_top_mem hΩ hAC hθ)
  have hv := woodinSparseRealizationMap_top hΩ hAC hθ
  rwa [woodinSparseRealizationMap_value hΩ hAC hθ ht, he] at hv

theorem woodinSparseQuotient_forced_transfer
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω)
    {i κ : V} (hi : i ∈ θ) [IsOrdinal κ]
    (hc : IterationQuotientClosedBelow A i θ κ) : IterationQuotientClosedBelow C i θ κ := by
  let := IsOrdinal.of_mem hi
  have hisub : i ⊆ Ω := fun x hx ↦ hθ x (IsOrdinal.toIsTransitive.transitive _ hi x hx)
  have hi' : i ∈ succ θ := mem_succ_iff.mpr (Or.inr hi)
  have hsi := woodinIterationStageCode_valid_le hΩ hAC hisub
  have hst := woodinIterationStageCode_valid_le hΩ hAC hθ
  have hci := woodinSparseStageCode_valid hΩ hAC hisub
  have hct := woodinSparseStageCode_valid hΩ hAC hθ
  unfold IterationQuotientClosedBelow at hc ⊢
  rw [(woodinIterationStage_old_row hΩ hAC hθ hi).1,
    (woodinIterationStage_old_row hΩ hAC hθ hi).2, woodinIterationStage_old_top hΩ hAC hθ hi] at hc
  rw [(woodinSparseStage_old_row hi').1, (woodinSparseStage_old_row hi').2,
    woodinSparseStageCode_all_tops hΩ hAC hθ hi']
  have hh := equivalentRetraction_quotient_closedBelow_forced
    (hsi.system.order.preorder i (mem_succ_self i)) (hsi.system.tops.top i (mem_succ_self i))
    (woodinNormalizationRec_retraction_le hΩ hAC hisub)
    ((woodinNormalizedStage_through_endpoint hΩ hAC hisub).1.system.order.preorder i (mem_succ_self i))
    (woodinNormalizedStage_top_mem hΩ hAC hisub)
    (fun _ hp ↦ (woodinNormalizationRec_equivalent_le hΩ hAC hisub hp).1)
    (woodinSparseStageMap_isomorphism hΩ hAC hisub) (hci.system.order.preorder i (mem_succ_self i))
    (woodinIterationStage_projection_to_row hΩ hAC hθ hi) (hst.system.order.preorder θ (mem_succ_self θ))
    (woodinSparseStage_projection_to_row hΩ hAC hθ hi) (hct.system.order.preorder θ (mem_succ_self θ))
    (woodinSparseRealizationMap_projection hΩ hAC hθ).maps
    (woodinSparseRealizationInverse_maps hΩ hAC hθ)
    (fun _ hq ↦ woodinSparseRealizationMap_right_inverse hΩ hAC hθ hq)
    (fun _ hp _ hq ↦ (woodinSparseRealizationMap_order_iff hΩ hAC hθ hp hq).symm)
    (fun p hp ↦ ?_) hc
  · simpa only [woodinSparseStageMap_raw_top hΩ hAC hisub] using hh
  · change ((forcingCodeπ C) ‘ ⟨i, θ⟩ₖ) ‘ ((woodinSparseRealizationMap θ) ‘ p) =
      (woodinSparseRealizationMap i) ‘ (((forcingCodeπ A) ‘ ⟨i, θ⟩ₖ) ‘ p)
    rw [woodinSparseStageCode_projection hΩ hAC hθ hi
      (function_value_mem (woodinSparseRealizationMap_projection hΩ hAC hθ).maps hp)]
    exact woodinSparseRealizationMap_restrict hΩ hAC hθ hi hp

theorem woodinSparseStageCode_final_quotient
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω)
    {i : V} (hi : i ∈ succ θ) :
    IterationQuotientClosedBelow C i θ ((kpair.π₂ (woodinIterationRec θ)) ‘ i) := by
  rcases mem_succ_iff.mp hi with rfl | hilow
  · exact (woodinSparseStageCode_valid hΩ hAC hθ).diagonal_quotient_closedBelow (mem_succ_self _) _
  · let := hΩ.inaccessible.1
    have hκ : IsOrdinal ((kpair.π₂ (woodinIterationRec θ)) ‘ i) := by
      rcases IsOrdinal.subset_iff.mp hθ with rfl | hθ
      · exact ((woodinIteration_endpoint_valid hΩ hAC).1.inaccessible i hi).1
      · exact (((woodinIterationExit hΩ hAC).2.1 θ hθ).1.inaccessible i hi).1
    let := hκ
    apply woodinSparseQuotient_forced_transfer hΩ hAC hθ hilow
    have hc : HasWoodinQuotientClosure (succ θ) A (kpair.π₂ (woodinIterationRec θ)) := by
      rcases IsOrdinal.subset_iff.mp hθ with rfl | hθ
      · exact (woodinIteration_endpoint_valid hΩ hAC).2
      · exact ((woodinIterationExit hΩ hAC).2.1 θ hθ).2
    exact hc i hi θ (mem_succ_self θ) (IsOrdinal.toIsTransitive.transitive _ hilow)

theorem woodinSparseStageCode_quotient_closure
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω) :
    HasWoodinQuotientClosure (succ θ) C (kpair.π₂ (woodinIterationRec θ)) := by
  intro i hi j hj hij
  let := IsOrdinal.of_mem hi
  rcases mem_succ_iff.mp hj with rfl | hj
  · exact woodinSparseStageCode_final_quotient hΩ hAC hθ hi
  · let := IsOrdinal.of_mem hj
    have hji : i ∈ succ j := mem_succ_iff.mpr (IsOrdinal.subset_iff.mp hij)
    have hjsub : j ⊆ Ω := fun x hx ↦ hθ x (IsOrdinal.toIsTransitive.transitive _ hj x hx)
    have hh := woodinSparseStageCode_final_quotient hΩ hAC hjsub hji
    rw [woodinIterationRec_old_cardinal hΩ hAC hjsub hji] at hh
    rw [woodinIterationRec_old_cardinal hΩ hAC hθ hi]
    exact ((woodinSparseStageCode_extends_previous hΩ hAC hθ hj).iterationQuotientClosedBelow_iff
      (woodinSparseStageCode_valid hΩ hAC hjsub) (woodinSparseStageCode_valid hΩ hAC hθ)
      hji (mem_succ_self j)).mp hh

theorem woodinSparsePrefixCode_quotient_closure
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω) :
    HasWoodinQuotientClosure θ (woodinSparsePrefixCode θ) (woodinIterationCardinalPrefix θ) := by
  intro i hi j hj hij
  let := IsOrdinal.of_mem hi
  let := IsOrdinal.of_mem hj
  have hji : i ∈ succ j := mem_succ_iff.mpr (IsOrdinal.subset_iff.mp hij)
  have hjsub : j ⊆ Ω := fun x hx ↦ hθ x (IsOrdinal.toIsTransitive.transitive _ hj x hx)
  have hh := woodinSparseStageCode_final_quotient hΩ hAC hjsub hji
  rw [woodinIterationRec_old_cardinal hΩ hAC hjsub hji] at hh
  rw [woodinIterationCardinalPrefix_value hΩ hAC hθ hi]
  exact ((woodinSparsePrefixCode_extends_stage hΩ hAC hθ hj).iterationQuotientClosedBelow_iff
    (woodinSparseStageCode_valid hΩ hAC hjsub) (woodinSparsePrefixCode_valid hΩ hAC hθ)
    hji (mem_succ_self j)).mp hh

end ZFVP


