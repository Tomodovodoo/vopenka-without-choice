import ZFVP.ModelTheory.WoodinSparseGeneric
import ZFVP.ModelTheory.EquivalentRetractionGenericContext
import ZFVP.ModelTheory.ForcingProjectionComposition

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable {Ω θ : V} [IsOrdinal θ]
local notation "A" => kpair.π₁ (woodinIterationRec θ)
local notation "N" => woodinNormalizedStageCode θ
local notation "C" => woodinSparseStageCode θ

theorem woodinNormalizedStage_top_mem
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω) :
    (forcingCodet A) ‘ θ ∈ (forcingCodeP N) ‘ θ := by
  have ht := ((woodinIterationStageCode_valid_le hΩ hAC hθ).system.tops.top θ (mem_succ_self θ)).1
  have hm := function_value_mem (woodinNormalizationRec_retraction_le hΩ hAC hθ).maps ht
  have he := (woodinNormalizationHistory_family_le hΩ hAC hθ).fixesTop θ (mem_succ_self θ)
  simp only [woodinNormalizationHistory_value (mem_succ_self θ)] at he
  rwa [he] at hm

variable (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω)
variable {G : Set V} (hG : IsExternalForcingGeneric
  ((forcingCodeP (kpair.π₁ (woodinIterationRec θ))) ‘ θ)
  ((forcingCodeR (kpair.π₁ (woodinIterationRec θ))) ‘ θ) G)

noncomputable def woodinIterationGenericContext : ForcingContext V :=
  ⟨(forcingCodeP A) ‘ θ, (forcingCodeR A) ‘ θ, (forcingCodet A) ‘ θ, G,
    (woodinIterationStageCode_valid_le hΩ hAC hθ).system.order.preorder θ (mem_succ_self θ),
    (woodinIterationStageCode_valid_le hΩ hAC hθ).system.tops.top θ (mem_succ_self θ), hG⟩

noncomputable def woodinSparseGenericContext : ForcingContext V :=
  (woodinIterationGenericContext hΩ hAC hθ hG).retractionIsomorphismImage
    (woodinNormalizationRec_retraction_le hΩ hAC hθ)
    ((woodinNormalizedStage_through_endpoint hΩ hAC hθ).1.system.order.preorder θ (mem_succ_self θ))
    (woodinNormalizedStage_top_mem hΩ hAC hθ)
    (woodinSparseStageMap_isomorphism hΩ hAC hθ)
    ((woodinSparseStageCode_valid hΩ hAC hθ).system.order.preorder θ (mem_succ_self θ))

theorem woodinSparseGenericContext_generic :
    (woodinSparseGenericContext hΩ hAC hθ hG).G = woodinSparseGeneric θ G :=
  forcingProjectionGeneric_comp (woodinSparseStageMap_isomorphism hΩ hAC hθ).projection
    (woodinNormalizationRec_retraction_le hΩ hAC hθ).projection
    ((woodinSparseStageCode_valid hΩ hAC hθ).system.order.preorder θ (mem_succ_self θ))
    ((woodinNormalizedStage_through_endpoint hΩ hAC hθ).1.system.order.preorder θ (mem_succ_self θ)) hG.1

theorem woodinSparseGenericContext_top : (woodinSparseGenericContext hΩ hAC hθ hG).one = ∅ := by
  have ht := ((woodinIterationStageCode_valid_le hΩ hAC hθ).system.tops.top θ (mem_succ_self θ)).1
  have he := (woodinNormalizationRec_retraction_le hΩ hAC hθ).fixes _
    (woodinNormalizedStage_top_mem hΩ hAC hθ)
  have hv := woodinSparseRealizationMap_top hΩ hAC hθ
  rw [woodinSparseRealizationMap_value hΩ hAC hθ ht, he] at hv
  exact hv

noncomputable def woodinSparseGenericModelEquiv :
    (woodinIterationGenericContext hΩ hAC hθ hG).Model ≃
      (woodinSparseGenericContext hΩ hAC hθ hG).Model :=
  (woodinIterationGenericContext hΩ hAC hθ hG).retractionIsomorphismImageEquiv
    (woodinNormalizationRec_retraction_le hΩ hAC hθ)
    ((woodinNormalizedStage_through_endpoint hΩ hAC hθ).1.system.order.preorder θ (mem_succ_self θ))
    (woodinNormalizedStage_top_mem hΩ hAC hθ)
    (fun _ hp ↦ (woodinNormalizationRec_equivalent_le hΩ hAC hθ hp).1)
    (woodinSparseStageMap_isomorphism hΩ hAC hθ)
    ((woodinSparseStageCode_valid hΩ hAC hθ).system.order.preorder θ (mem_succ_self θ))

theorem woodinSparseGenericModelEquiv_mem
    (x y : (woodinIterationGenericContext hΩ hAC hθ hG).Model) :
    woodinSparseGenericModelEquiv hΩ hAC hθ hG x ∈ woodinSparseGenericModelEquiv hΩ hAC hθ hG y ↔ x ∈ y :=
  (woodinIterationGenericContext hΩ hAC hθ hG).retractionIsomorphismImageEquiv_mem
    (woodinNormalizationRec_retraction_le hΩ hAC hθ)
    ((woodinNormalizedStage_through_endpoint hΩ hAC hθ).1.system.order.preorder θ (mem_succ_self θ))
    (woodinNormalizedStage_top_mem hΩ hAC hθ)
    (fun _ hp ↦ (woodinNormalizationRec_equivalent_le hΩ hAC hθ hp).1)
    (woodinSparseStageMap_isomorphism hΩ hAC hθ)
    ((woodinSparseStageCode_valid hΩ hAC hθ).system.order.preorder θ (mem_succ_self θ)) x y

theorem woodinSparseGenericModelEquiv_check (x : V) :
    woodinSparseGenericModelEquiv hΩ hAC hθ hG ((woodinIterationGenericContext hΩ hAC hθ hG).check x) =
      (woodinSparseGenericContext hΩ hAC hθ hG).check x :=
  (woodinIterationGenericContext hΩ hAC hθ hG).retractionIsomorphismImageEquiv_check
    (woodinNormalizationRec_retraction_le hΩ hAC hθ)
    ((woodinNormalizedStage_through_endpoint hΩ hAC hθ).1.system.order.preorder θ (mem_succ_self θ))
    (woodinNormalizedStage_top_mem hΩ hAC hθ)
    (fun _ hp ↦ (woodinNormalizationRec_equivalent_le hΩ hAC hθ hp).1)
    (woodinSparseStageMap_isomorphism hΩ hAC hθ)
    ((woodinSparseStageCode_valid hΩ hAC hθ).system.order.preorder θ (mem_succ_self θ)) x

theorem woodinSparseGenericModelEquiv_name (τ : ForcingName ((forcingCodeP A) ‘ θ)) :
    woodinSparseGenericModelEquiv hΩ hAC hθ hG ((woodinIterationGenericContext hΩ hAC hθ hG).ofName τ) =
      (woodinSparseGenericContext hΩ hAC hθ hG).ofName
        ⟨nameAction (woodinSparseRealizationMap θ) τ.val,
          nameAction_isName (woodinSparseRealizationMap_projection hΩ hAC hθ).maps τ.property⟩ :=
  (woodinIterationGenericContext hΩ hAC hθ hG).retractionIsomorphismImageEquiv_name
    (woodinNormalizationRec_retraction_le hΩ hAC hθ)
    ((woodinNormalizedStage_through_endpoint hΩ hAC hθ).1.system.order.preorder θ (mem_succ_self θ))
    (woodinNormalizedStage_top_mem hΩ hAC hθ)
    (fun _ hp ↦ (woodinNormalizationRec_equivalent_le hΩ hAC hθ hp).1)
    (woodinSparseStageMap_isomorphism hΩ hAC hθ)
    ((woodinSparseStageCode_valid hΩ hAC hθ).system.order.preorder θ (mem_succ_self θ)) τ

end ZFVP
