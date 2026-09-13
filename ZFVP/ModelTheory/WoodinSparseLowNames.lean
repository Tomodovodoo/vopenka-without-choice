import ZFVP.ModelTheory.WoodinSparseLowNameTransport
import ZFVP.ModelTheory.WoodinSparseGenericContext
import ZFVP.ModelTheory.WoodinSparseMarkedRank
import ZFVP.ModelTheory.WoodinSparseExactRank
import ZFVP.ModelTheory.WoodinEndpointLowNames
import ZFVP.ModelTheory.WoodinFixedPointLowNames
import ZFVP.ModelTheory.SuccessorLowNameCoverage

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

private theorem forcingContext_eq_of_data (A B : ForcingContext V)
    (hP : A.P = (B).P) (hR : A.R = B.R) (ht : A.one = B.one) (hG : A.G = B.G) : A = B := by
  cases A
  cases B
  cases hP
  cases hR
  cases ht
  cases hG
  rfl

variable {Ω : V} [IsOrdinal Ω]
variable (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) {G : Set V}
  (hG : IsExternalForcingGeneric
    ((forcingCodeP (kpair.π₁ (woodinIterationRec Ω))) ‘ Ω)
    ((forcingCodeR (kpair.π₁ (woodinIterationRec Ω))) ‘ Ω) G)

local notation "E" => woodinSparseGenericContext hΩ hAC (subset_refl Ω) hG

theorem woodinSparseGenericContext_endpoint_low_name_coverage :
    ∀ x ∈ hierarchy ((E).check Ω), ∃ τ : ForcingName (E).P,
      τ.val ∈ hierarchy Ω ∧ x = (E).ofName τ := by
  let A := woodinIterationGenericContext hΩ hAC (subset_refl Ω) hG
  have hcov : A.HasLocalLowNameCoverage Ω (woodinStageCarrier Ω) (woodinStageMap Ω) := by
    intro x hx
    obtain ⟨τ, hτ, hx⟩ := (WoodinEndpointModel.mem_rank_iff_localName hΩ hAC hG x).mp hx
    exact ⟨τ.val, hτ, τ.property,
      ⟨nameAction (woodinStageMap Ω) τ.val,
        nameAction_isName (woodinStageMap_endpoint_maps hΩ hAC) τ.property⟩, rfl, hx⟩
  exact woodinSparseGenericContext_low_name_coverage_of_local hΩ hAC (subset_refl Ω) hG
    hΩ.inaccessible (woodinStageMap_endpoint_maps hΩ hAC)
    (woodinSparseStageCode_rows_subset_at_endpoint hΩ hAC Ω (mem_succ_self Ω)) hcov

variable {γ : V} [IsOrdinal γ] (hγ : γ ∈ Ω)

omit [IsOrdinal γ] in
theorem woodinFixedPoint_stage_generic :
    IsExternalForcingGeneric
      ((forcingCodeP (kpair.π₁ (woodinIterationRec γ))) ‘ γ)
      ((forcingCodeR (kpair.π₁ (woodinIterationRec γ))) ‘ γ)
      (WoodinEndpointModel.stageContext hΩ hAC hG hγ).G := by
  have h := (WoodinEndpointModel.stageContext hΩ hAC hG hγ).generic
  change IsExternalForcingGeneric
    ((forcingCodeP (kpair.π₁ (woodinIterationRec Ω))) ‘ γ)
    ((forcingCodeR (kpair.π₁ (woodinIterationRec Ω))) ‘ γ) _ at h
  rwa [(woodinIterationStage_old_row hΩ hAC (subset_refl Ω) hγ).1,
    (woodinIterationStage_old_row hΩ hAC (subset_refl Ω) hγ).2] at h

noncomputable def woodinSparseFixedPointContext : ForcingContext V :=
  woodinSparseGenericContext hΩ hAC (IsOrdinal.toIsTransitive.transitive _ hγ)
    (woodinFixedPoint_stage_generic hΩ hAC hG hγ)

local notation "B" => woodinSparseFixedPointContext hΩ hAC hG hγ

theorem woodinFixedPoint_rawContext_eq_stageContext :
    woodinIterationGenericContext hΩ hAC (IsOrdinal.toIsTransitive.transitive _ hγ)
      (woodinFixedPoint_stage_generic hΩ hAC hG hγ) =
        WoodinEndpointModel.stageContext hΩ hAC hG hγ := by
  apply forcingContext_eq_of_data
  · exact (woodinIterationStage_old_row hΩ hAC (subset_refl Ω) hγ).1.symm
  · exact (woodinIterationStage_old_row hΩ hAC (subset_refl Ω) hγ).2.symm
  · exact (woodinIterationStage_old_top hΩ hAC (subset_refl Ω) hγ).symm
  · rfl

omit [IsOrdinal γ] in
include hΩ hAC hγ in
theorem woodinStageMap_fixedPoint_maps_rawStage
    (hfix : (kpair.π₂ (woodinIterationRec Ω)) ‘ γ = γ) :
    woodinStageMap γ ∈ ((forcingCodeP (kpair.π₁ (woodinIterationRec γ))) ‘ γ) ^ woodinStageCarrier γ := by
  rw [← (woodinIterationStage_old_row hΩ hAC (subset_refl Ω) hγ).1]
  exact woodinStageMap_fixedPoint_maps hΩ hAC hγ hfix

theorem woodinFixedPoint_rawContext_local_coverage
    (hfix : (kpair.π₂ (woodinIterationRec Ω)) ‘ γ = γ) :
    (woodinIterationGenericContext hΩ hAC (IsOrdinal.toIsTransitive.transitive _ hγ)
      (woodinFixedPoint_stage_generic hΩ hAC hG hγ)).HasLocalLowNameCoverage
        γ (woodinStageCarrier γ) (woodinStageMap γ) := by
  apply (ForcingContext.hasLocalLowNameCoverage_congr
    (woodinFixedPoint_rawContext_eq_stageContext hΩ hAC hG hγ)
    γ (woodinStageCarrier γ) (woodinStageMap γ)).mpr
  intro x hx
  obtain ⟨τ, hτ, hx⟩ :=
    (WoodinEndpointModel.fixedPoint_mem_rank_iff_localName hΩ hAC hG hγ hfix x).mp hx
  exact ⟨τ.val, hτ, τ.property,
    ⟨nameAction (woodinStageMap γ) τ.val,
      nameAction_isName (woodinStageMap_fixedPoint_maps hΩ hAC hγ hfix) τ.property⟩, rfl, hx⟩

theorem woodinSparseFixedPointContext_low_name_coverage
    (hfix : (kpair.π₂ (woodinIterationRec Ω)) ‘ γ = γ) :
    ∀ x ∈ hierarchy ((B).check γ), ∃ τ : ForcingName (B).P,
      τ.val ∈ hierarchy γ ∧ x = (B).ofName τ :=
  woodinSparseGenericContext_low_name_coverage_of_local hΩ hAC
    (IsOrdinal.toIsTransitive.transitive _ hγ) (woodinFixedPoint_stage_generic hΩ hAC hG hγ)
    (woodinIteration_fixedPoint_inaccessible hΩ hAC hγ hfix)
    (woodinStageMap_fixedPoint_maps_rawStage hΩ hAC hγ hfix)
    (woodinSparseStageCode_rows_subset_at_fixedPoint hΩ hAC hγ hfix γ (mem_succ_self γ))
    (woodinFixedPoint_rawContext_local_coverage hΩ hAC hG hγ hfix)

end ZFVP


