import ZFVP.ModelTheory.WoodinSparseBetweenInclusion
import ZFVP.ModelTheory.ForcingContextCongruence
import ZFVP.ModelTheory.ForcingContextEquivCongruence
import ZFVP.ModelTheory.ForcingBaseChange
import ZFVP.ModelTheory.TwoStepInclusion
import ZFVP.SetTheory.UniformRank

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable {Ω γ : V} [IsOrdinal Ω] [IsOrdinal γ]
variable (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) {G : Set V}
  (hG : IsExternalForcingGeneric
    ((forcingCodeP (kpair.π₁ (woodinIterationRec Ω))) ‘ Ω)
    ((forcingCodeR (kpair.π₁ (woodinIterationRec Ω))) ‘ Ω) G)
  (hγ : γ ∈ Ω)
local notation "A" => woodinSparseFixedPointContext hΩ hAC hG hγ
local notation "E" => woodinSparseGenericContext hΩ hAC (subset_refl Ω) hG
local notation "RawA" => WoodinEndpointModel.stageContext hΩ hAC hG hγ
local notation "RawE" => WoodinEndpointModel.context hΩ hAC hG

noncomputable def woodinSparseFixedPointContext_rawEquiv : (RawA).Model ≃ (A).Model :=
  (ForcingContext.modelCongr (woodinFixedPoint_rawContext_eq_stageContext hΩ hAC hG hγ).symm).trans
    (woodinSparseGenericModelEquiv hΩ hAC (IsOrdinal.toIsTransitive.transitive _ hγ)
      (woodinFixedPoint_stage_generic hΩ hAC hG hγ))

theorem woodinSparseFixedPointContext_rawEquiv_mem (x y : (RawA).Model) :
    woodinSparseFixedPointContext_rawEquiv hΩ hAC hG hγ x ∈
      woodinSparseFixedPointContext_rawEquiv hΩ hAC hG hγ y ↔ x ∈ y := by
  exact ForcingContext.modelCongr_trans_mem
    (woodinFixedPoint_rawContext_eq_stageContext hΩ hAC hG hγ).symm
    (woodinSparseGenericModelEquiv hΩ hAC (IsOrdinal.toIsTransitive.transitive _ hγ)
      (woodinFixedPoint_stage_generic hΩ hAC hG hγ))
    (woodinSparseGenericModelEquiv_mem hΩ hAC (IsOrdinal.toIsTransitive.transitive _ hγ)
      (woodinFixedPoint_stage_generic hΩ hAC hG hγ)) x y

theorem woodinSparseFixedPointContext_rawEquiv_check (x : V) :
    woodinSparseFixedPointContext_rawEquiv hΩ hAC hG hγ ((RawA).check x) = (A).check x := by
  exact ForcingContext.modelCongr_trans_check
    (woodinFixedPoint_rawContext_eq_stageContext hΩ hAC hG hγ).symm
    (woodinSparseGenericModelEquiv hΩ hAC (IsOrdinal.toIsTransitive.transitive _ hγ)
      (woodinFixedPoint_stage_generic hΩ hAC hG hγ))
    (woodinSparseGenericModelEquiv_check hΩ hAC (IsOrdinal.toIsTransitive.transitive _ hγ)
      (woodinFixedPoint_stage_generic hΩ hAC hG hγ)) x

noncomputable def woodinSparseEndpoint_rawEquiv : (RawE).Model ≃ (E).Model :=
  woodinSparseGenericModelEquiv hΩ hAC (subset_refl Ω) hG

theorem woodinSparseEndpoint_rawEquiv_mem (x y : (RawE).Model) :
    woodinSparseEndpoint_rawEquiv hΩ hAC hG x ∈ woodinSparseEndpoint_rawEquiv hΩ hAC hG y ↔ x ∈ y :=
  woodinSparseGenericModelEquiv_mem hΩ hAC (subset_refl Ω) hG x y

theorem woodinSparseEndpoint_rawEquiv_check (x : V) :
    woodinSparseEndpoint_rawEquiv hΩ hAC hG ((RawE).check x) = (E).check x :=
  woodinSparseGenericModelEquiv_check hΩ hAC (subset_refl Ω) hG x

theorem woodinSparseFixedPointContext_inclusion_commutes (x : (RawA).Model) :
    woodinSparseFixedPointContext_inclusion hΩ hAC hG hγ
      (woodinSparseFixedPointContext_rawEquiv hΩ hAC hG hγ x) =
        woodinSparseEndpoint_rawEquiv hΩ hAC hG (WoodinEndpointModel.stageInclusion hΩ hAC hG hγ x) := by
  let a := MembershipEndExtension.ofEquiv (woodinSparseFixedPointContext_rawEquiv hΩ hAC hG hγ)
    (woodinSparseFixedPointContext_rawEquiv_mem hΩ hAC hG hγ)
  let b := MembershipEndExtension.ofEquiv (woodinSparseEndpoint_rawEquiv hΩ hAC hG)
    (woodinSparseEndpoint_rawEquiv_mem hΩ hAC hG)
  apply (RawA).endExtension_ext
    ((woodinSparseFixedPointContext_inclusion hΩ hAC hG hγ).comp a)
    (b.comp (WoodinEndpointModel.stageInclusion hΩ hAC hG hγ))
  intro u
  change woodinSparseFixedPointContext_inclusion hΩ hAC hG hγ
      (woodinSparseFixedPointContext_rawEquiv hΩ hAC hG hγ ((RawA).check u)) =
    woodinSparseEndpoint_rawEquiv hΩ hAC hG
      (WoodinEndpointModel.stageInclusion hΩ hAC hG hγ ((RawA).check u))
  rw [woodinSparseFixedPointContext_rawEquiv_check, woodinSparseFixedPointContext_inclusion_check]
  have hc : WoodinEndpointModel.stageInclusion hΩ hAC hG hγ ((RawA).check u) = (RawE).check u :=
    ForcingContext.projectionInclusion_check (RawA) (RawE)
      (WoodinEndpointModel.stage_splitProjection hΩ hAC hG hγ) rfl u
  rw [hc, woodinSparseEndpoint_rawEquiv_check]

theorem woodinSparseFixedPointContext_inclusion_hierarchy :
    woodinSparseFixedPointContext_inclusion hΩ hAC hG hγ (hierarchy ((A).check γ)) =
      hierarchy ((E).check γ) := by
  let a := ElementaryMap.ofMembershipIso (woodinSparseFixedPointContext_rawEquiv hΩ hAC hG hγ)
    (woodinSparseFixedPointContext_rawEquiv_mem hΩ hAC hG hγ)
  let b := ElementaryMap.ofMembershipIso (woodinSparseEndpoint_rawEquiv hΩ hAC hG)
    (woodinSparseEndpoint_rawEquiv_mem hΩ hAC hG)
  have ha : woodinSparseFixedPointContext_rawEquiv hΩ hAC hG hγ (hierarchy ((RawA).check γ)) =
      hierarchy ((A).check γ) := by
    exact (a.map_hierarchy ((RawA).check γ)).trans
      (congrArg hierarchy (woodinSparseFixedPointContext_rawEquiv_check hΩ hAC hG hγ γ))
  have hb : woodinSparseEndpoint_rawEquiv hΩ hAC hG (hierarchy ((RawE).check γ)) =
      hierarchy ((E).check γ) := by
    exact (b.map_hierarchy ((RawE).check γ)).trans
      (congrArg hierarchy (woodinSparseEndpoint_rawEquiv_check hΩ hAC hG γ))
  rw [← ha, woodinSparseFixedPointContext_inclusion_commutes,
    WoodinEndpointModel.stageInclusion_hierarchy, hb]

end ZFVP

