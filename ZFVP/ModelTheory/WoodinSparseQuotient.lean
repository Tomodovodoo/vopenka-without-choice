import ZFVP.ModelTheory.WoodinSparseQuotientInputs
import ZFVP.ModelTheory.QuotientEquivalenceTransport
import ZFVP.ModelTheory.QuotientEquivalenceClosure

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable {Ω θ i : V} [IsOrdinal θ] [IsOrdinal i]
variable (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω) (hi : i ∈ θ)
variable {G : Set V} (hG : IsExternalForcingGeneric
  ((forcingCodeP (kpair.π₁ (woodinIterationRec i))) ‘ i)
  ((forcingCodeR (kpair.π₁ (woodinIterationRec i))) ‘ i) G)

include hθ hi in
omit [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [IsOrdinal i] in
private theorem earlier_subset : i ⊆ Ω := fun x hx ↦ hθ x (IsOrdinal.toIsTransitive.transitive _ hi x hx)

local notation "A" => kpair.π₁ (woodinIterationRec θ)
local notation "C" => woodinSparseStageCode θ
local notation "R₀" => woodinIterationGenericContext hΩ hAC (earlier_subset hθ hi) hG
local notation "S₀" => woodinSparseGenericContext hΩ hAC (earlier_subset hθ hi) hG
local notation "e" => woodinSparseGenericModelEquiv hΩ hAC (earlier_subset hθ hi) hG

theorem woodinSparseQuotient_splitProjection :
    IsForcingSplitProjection
      ((R₀).transportedProjectionQuotient S₀ e ((forcingCodeP C) ‘ θ) ((forcingCodeπ C) ‘ ⟨i, θ⟩ₖ))
      ((R₀).transportedProjectionQuotientOrder S₀ e ((forcingCodeP C) ‘ θ)
        ((forcingCodeR C) ‘ θ) ((forcingCodeπ C) ‘ ⟨i, θ⟩ₖ))
      ((R₀).projectionQuotient ((forcingCodeP A) ‘ θ) ((forcingCodeπ A) ‘ ⟨i, θ⟩ₖ))
      ((R₀).projectionQuotientOrder ((forcingCodeP A) ‘ θ) ((forcingCodeR A) ‘ θ) ((forcingCodeπ A) ‘ ⟨i, θ⟩ₖ))
      ((R₀).projectionQuotientMap ((forcingCodeP A) ‘ θ) ((forcingCodeπ A) ‘ ⟨i, θ⟩ₖ) (woodinSparseRealizationMap θ))
      ((R₀).transportedProjectionQuotientInverse S₀ e ((forcingCodeP C) ‘ θ)
        ((forcingCodeπ C) ‘ ⟨i, θ⟩ₖ) (woodinSparseRealizationInverse θ)) := by
  apply (R₀).transportedProjectionQuotient_splitProjection S₀ e
    (woodinSparseGenericModelEquiv_mem hΩ hAC (earlier_subset hθ hi) hG)
    (woodinSparseGenericModelEquiv_check hΩ hAC (earlier_subset hθ hi) hG)
    (woodinIterationStage_projection_to_row hΩ hAC hθ hi).maps
    (woodinSparseStage_projection_to_row hΩ hAC hθ hi).maps
    (woodinSparseRealizationMap_projection hΩ hAC hθ).maps
    (woodinSparseRealizationInverse_maps hΩ hAC hθ)
    ?_ (fun _ hq ↦ woodinSparseRealizationMap_right_inverse hΩ hAC hθ hq)
    (fun _ hp _ hq ↦ (woodinSparseRealizationMap_order_iff hΩ hAC hθ hp hq).symm)
  intro p hp
  rw [woodinSparseGenericContext_generic]
  exact woodinSparseGeneric_quotient_projection_iff hΩ hAC hθ hi hp hG.1

theorem woodinSparseQuotient_order_iff
    (x : (R₀).Model) (hx : x ∈ (R₀).projectionQuotient ((forcingCodeP A) ‘ θ) ((forcingCodeπ A) ‘ ⟨i, θ⟩ₖ))
    (y : (R₀).Model) (hy : y ∈ (R₀).projectionQuotient ((forcingCodeP A) ‘ θ) ((forcingCodeπ A) ‘ ⟨i, θ⟩ₖ)) :
    ⟨((R₀).projectionQuotientMap ((forcingCodeP A) ‘ θ) ((forcingCodeπ A) ‘ ⟨i, θ⟩ₖ) (woodinSparseRealizationMap θ)) ‘ x,
      ((R₀).projectionQuotientMap ((forcingCodeP A) ‘ θ) ((forcingCodeπ A) ‘ ⟨i, θ⟩ₖ) (woodinSparseRealizationMap θ)) ‘ y⟩ₖ ∈
        (R₀).transportedProjectionQuotientOrder S₀ e ((forcingCodeP C) ‘ θ) ((forcingCodeR C) ‘ θ) ((forcingCodeπ C) ‘ ⟨i, θ⟩ₖ) ↔
      ⟨x, y⟩ₖ ∈ (R₀).projectionQuotientOrder ((forcingCodeP A) ‘ θ) ((forcingCodeR A) ‘ θ) ((forcingCodeπ A) ‘ ⟨i, θ⟩ₖ) := by
  apply (R₀).transportedProjectionQuotientMap_order_iff S₀ e
    (woodinSparseGenericModelEquiv_mem hΩ hAC (earlier_subset hθ hi) hG)
    (woodinSparseGenericModelEquiv_check hΩ hAC (earlier_subset hθ hi) hG)
    (woodinIterationStage_projection_to_row hΩ hAC hθ hi).maps
    (woodinSparseStage_projection_to_row hΩ hAC hθ hi).maps
    (woodinSparseRealizationMap_projection hΩ hAC hθ).maps ?_
    (fun _ hp _ hq ↦ (woodinSparseRealizationMap_order_iff hΩ hAC hθ hp hq).symm) x hx y hy
  intro p hp
  rw [woodinSparseGenericContext_generic]
  exact woodinSparseGeneric_quotient_projection_iff hΩ hAC hθ hi hp hG.1

theorem woodinSparseQuotient_closedBelow_iff (κ : V) [IsOrdinal κ] :
    IsForcingClosedBelow
      ((R₀).projectionQuotient ((forcingCodeP A) ‘ θ) ((forcingCodeπ A) ‘ ⟨i, θ⟩ₖ))
      (forcingSeparativeOrder
        ((R₀).projectionQuotient ((forcingCodeP A) ‘ θ) ((forcingCodeπ A) ‘ ⟨i, θ⟩ₖ))
        ((R₀).projectionQuotientOrder ((forcingCodeP A) ‘ θ) ((forcingCodeR A) ‘ θ) ((forcingCodeπ A) ‘ ⟨i, θ⟩ₖ)))
      ((R₀).check κ) ↔
    IsForcingClosedBelow
      ((S₀).projectionQuotient ((forcingCodeP C) ‘ θ) ((forcingCodeπ C) ‘ ⟨i, θ⟩ₖ))
      (forcingSeparativeOrder
        ((S₀).projectionQuotient ((forcingCodeP C) ‘ θ) ((forcingCodeπ C) ‘ ⟨i, θ⟩ₖ))
        ((S₀).projectionQuotientOrder ((forcingCodeP C) ‘ θ) ((forcingCodeR C) ‘ θ) ((forcingCodeπ C) ‘ ⟨i, θ⟩ₖ)))
      ((S₀).check κ) := by
  apply (R₀).projectionQuotient_equivalence_closedBelow_check_iff S₀ e
    (woodinSparseGenericModelEquiv_mem hΩ hAC (earlier_subset hθ hi) hG)
    (woodinSparseGenericModelEquiv_check hΩ hAC (earlier_subset hθ hi) hG)
    (woodinIterationStage_projection_to_row hΩ hAC hθ hi).maps
    (woodinSparseStage_projection_to_row hΩ hAC hθ hi).maps
    (woodinSparseRealizationMap_projection hΩ hAC hθ).maps
    (woodinSparseRealizationInverse_maps hΩ hAC hθ)
    ?_ (fun _ hq ↦ woodinSparseRealizationMap_right_inverse hΩ hAC hθ hq)
    (fun _ hp _ hq ↦ (woodinSparseRealizationMap_order_iff hΩ hAC hθ hp hq).symm) κ
  intro p hp
  rw [woodinSparseGenericContext_generic]
  exact woodinSparseGeneric_quotient_projection_iff hΩ hAC hθ hi hp hG.1

end ZFVP

