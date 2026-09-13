import ZFVP.ModelTheory.WoodinSparseRealizationColumns
import ZFVP.ModelTheory.ForcingReflectingProjection

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable {Ω θ : V} [IsOrdinal θ]
local notation "A" => kpair.π₁ (woodinIterationRec θ)
local notation "C" => woodinSparseStageCode θ

def woodinSparseGeneric (θ : V) (G : Set V) : Set V :=
  forcingProjectionGeneric ((forcingCodeP (woodinSparseStageCode θ)) ‘ θ)
    ((forcingCodeR (woodinSparseStageCode θ)) ‘ θ) (woodinSparseRealizationMap θ) G

theorem woodinSparseRealizationMap_surjective
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω) :
    ∀ q ∈ (forcingCodeP C) ‘ θ, ∃ p ∈ (forcingCodeP A) ‘ θ,
      (woodinSparseRealizationMap θ) ‘ p = q := by
  intro q hq
  exact ⟨(woodinSparseRealizationInverse θ) ‘ q,
    function_value_mem (woodinSparseRealizationInverse_maps hΩ hAC hθ) hq,
    woodinSparseRealizationMap_right_inverse hΩ hAC hθ hq⟩

theorem woodinSparseGeneric_filter
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω)
    {G : Set V} (hG : IsExternalForcingFilter ((forcingCodeP A) ‘ θ) ((forcingCodeR A) ‘ θ) G) :
    IsExternalForcingFilter ((forcingCodeP C) ‘ θ) ((forcingCodeR C) ‘ θ) (woodinSparseGeneric θ G) :=
  (woodinSparseRealizationMap_projection hΩ hAC hθ).filter
    ((woodinSparseStageCode_valid hΩ hAC hθ).system.order.preorder θ (mem_succ_self θ)) hG

theorem woodinSparseGeneric_generic
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω)
    {G : Set V} (hG : IsExternalForcingGeneric ((forcingCodeP A) ‘ θ) ((forcingCodeR A) ‘ θ) G) :
    IsExternalForcingGeneric ((forcingCodeP C) ‘ θ) ((forcingCodeR C) ‘ θ) (woodinSparseGeneric θ G) :=
  (woodinSparseRealizationMap_projection hΩ hAC hθ).generic
    ((woodinSparseStageCode_valid hΩ hAC hθ).system.order.preorder θ (mem_succ_self θ)) hG

theorem woodinSparseGeneric_member_iff
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω)
    {G : Set V} (hG : IsExternalForcingFilter ((forcingCodeP A) ‘ θ) ((forcingCodeR A) ‘ θ) G)
    {p : V} (hp : p ∈ (forcingCodeP A) ‘ θ) :
    (woodinSparseRealizationMap θ) ‘ p ∈ woodinSparseGeneric θ G ↔ p ∈ G :=
  (woodinSparseRealizationMap_projection hΩ hAC hθ).image_member_iff
    (fun _ hp _ hq ↦ (woodinSparseRealizationMap_order_iff hΩ hAC hθ hp hq).mpr)
    ((woodinSparseStageCode_valid hΩ hAC hθ).system.order.preorder θ (mem_succ_self θ)) hG hp

theorem woodinSparseGeneric_preimage_generic
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω)
    {H : Set V} (hH : IsExternalForcingGeneric ((forcingCodeP C) ‘ θ) ((forcingCodeR C) ‘ θ) H) :
    IsExternalForcingGeneric ((forcingCodeP A) ‘ θ) ((forcingCodeR A) ‘ θ)
      (forcingProjectionPreimage ((forcingCodeP A) ‘ θ) (woodinSparseRealizationMap θ) H) :=
  (woodinSparseRealizationMap_projection hΩ hAC hθ).preimage_generic
    (fun _ hp _ hq ↦ (woodinSparseRealizationMap_order_iff hΩ hAC hθ hp hq).mpr)
    (woodinSparseRealizationMap_surjective hΩ hAC hθ) hH

theorem woodinSparseGeneric_preimage_image
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω)
    {G : Set V} (hG : IsExternalForcingFilter ((forcingCodeP A) ‘ θ) ((forcingCodeR A) ‘ θ) G) :
    forcingProjectionPreimage ((forcingCodeP A) ‘ θ) (woodinSparseRealizationMap θ)
      (woodinSparseGeneric θ G) = G :=
  (woodinSparseRealizationMap_projection hΩ hAC hθ).preimage_image
    (fun _ hp _ hq ↦ (woodinSparseRealizationMap_order_iff hΩ hAC hθ hp hq).mpr)
    ((woodinSparseStageCode_valid hΩ hAC hθ).system.order.preorder θ (mem_succ_self θ)) hG

theorem woodinSparseGeneric_image_preimage
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω)
    {H : Set V} (hH : IsExternalForcingFilter ((forcingCodeP C) ‘ θ) ((forcingCodeR C) ‘ θ) H) :
    woodinSparseGeneric θ
      (forcingProjectionPreimage ((forcingCodeP A) ‘ θ) (woodinSparseRealizationMap θ) H) = H :=
  (woodinSparseRealizationMap_projection hΩ hAC hθ).image_preimage
    (woodinSparseRealizationMap_surjective hΩ hAC hθ)
    ((woodinSparseStageCode_valid hΩ hAC hθ).system.order.preorder θ (mem_succ_self θ)) hH

theorem woodinSparseGeneric_quotient_member_iff
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω)
    {i p : V} (hi : i ∈ θ) (hp : p ∈ (forcingCodeP A) ‘ θ)
    {G : Set V} (hG : IsExternalForcingFilter
      ((forcingCodeP (kpair.π₁ (woodinIterationRec i))) ‘ i)
      ((forcingCodeR (kpair.π₁ (woodinIterationRec i))) ‘ i) G) :
    ((woodinSparseRealizationMap θ) ‘ p) ↾ (succ (woodinSourceIndex i)) ∈ woodinSparseGeneric i G ↔
      ((forcingCodeπ A) ‘ ⟨i, θ⟩ₖ) ‘ p ∈ G := by
  let := IsOrdinal.of_mem hi
  let := hΩ.inaccessible.1
  have hisub : i ⊆ Ω := IsOrdinal.toIsTransitive.transitive _ (hθ i hi)
  rw [woodinSparseRealizationMap_restrict hΩ hAC hθ hi hp]
  apply woodinSparseGeneric_member_iff hΩ hAC hisub hG
  rw [← (woodinIterationStage_old_row hΩ hAC hθ hi).1]
  exact (woodinIterationStageCode_valid_le hΩ hAC hθ).system.split.projMaps i
    (mem_succ_iff.mpr (Or.inr hi)) θ (mem_succ_self θ)
    (IsOrdinal.toIsTransitive.transitive _ hi) p hp

end ZFVP
