import ZFVP.ModelTheory.WoodinSparseGenericContext
import ZFVP.ModelTheory.IterationSystemProjection

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable {Ω θ : V} [IsOrdinal θ]
local notation "A" => kpair.π₁ (woodinIterationRec θ)
local notation "C" => woodinSparseStageCode θ

omit [IsOrdinal θ] in
theorem woodinSparseStage_old_row {i : V} (hi : i ∈ succ θ) :
    (forcingCodeP C) ‘ i = (forcingCodeP (woodinSparseStageCode i)) ‘ i ∧
    (forcingCodeR C) ‘ i = (forcingCodeR (woodinSparseStageCode i)) ‘ i := by
  simp only [woodinSparseStageCode, forcingRecodedCode, forcingCodeP_code, forcingCodeR_code,
    (woodinSparseRecodingHistory_values hi).1, (woodinSparseRecodingHistory_values hi).2.1,
    (woodinSparseRecodingHistory_values (mem_succ_self i)).1,
    (woodinSparseRecodingHistory_values (mem_succ_self i)).2.1, and_self]

theorem woodinIterationStage_projection_to_row
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω)
    {i : V} (hi : i ∈ θ) :
    IsForcingProjection
      ((forcingCodeP (kpair.π₁ (woodinIterationRec i))) ‘ i)
      ((forcingCodeR (kpair.π₁ (woodinIterationRec i))) ‘ i)
      ((forcingCodeP A) ‘ θ) ((forcingCodeR A) ‘ θ) ((forcingCodeπ A) ‘ ⟨i, θ⟩ₖ) := by
  rw [← (woodinIterationStage_old_row hΩ hAC hθ hi).1,
    ← (woodinIterationStage_old_row hΩ hAC hθ hi).2]
  exact (woodinIterationStageCode_valid_le hΩ hAC hθ).system.projection
    (mem_succ_iff.mpr (Or.inr hi)) (mem_succ_self θ) (IsOrdinal.toIsTransitive.transitive _ hi)

theorem woodinSparseStage_projection_to_row
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω)
    {i : V} (hi : i ∈ θ) :
    IsForcingProjection ((forcingCodeP (woodinSparseStageCode i)) ‘ i)
      ((forcingCodeR (woodinSparseStageCode i)) ‘ i)
      ((forcingCodeP C) ‘ θ) ((forcingCodeR C) ‘ θ) ((forcingCodeπ C) ‘ ⟨i, θ⟩ₖ) := by
  have hi' : i ∈ succ θ := mem_succ_iff.mpr (Or.inr hi)
  rw [← (woodinSparseStage_old_row hi').1, ← (woodinSparseStage_old_row hi').2]
  exact (woodinSparseStageCode_valid hΩ hAC hθ).system.projection
    hi' (mem_succ_self θ) (IsOrdinal.toIsTransitive.transitive _ hi)

theorem woodinSparseGeneric_quotient_projection_iff
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω)
    {i p : V} (hi : i ∈ θ) (hp : p ∈ (forcingCodeP A) ‘ θ)
    {G : Set V} (hG : IsExternalForcingFilter
      ((forcingCodeP (kpair.π₁ (woodinIterationRec i))) ‘ i)
      ((forcingCodeR (kpair.π₁ (woodinIterationRec i))) ‘ i) G) :
    ((forcingCodeπ C) ‘ ⟨i, θ⟩ₖ) ‘ ((woodinSparseRealizationMap θ) ‘ p) ∈ woodinSparseGeneric i G ↔
      ((forcingCodeπ A) ‘ ⟨i, θ⟩ₖ) ‘ p ∈ G := by
  rw [woodinSparseStageCode_projection hΩ hAC hθ hi
    (function_value_mem (woodinSparseRealizationMap_projection hΩ hAC hθ).maps hp)]
  exact woodinSparseGeneric_quotient_member_iff hΩ hAC hθ hi hp hG

theorem woodinSparseGeneric_quotient_inverse_iff
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω)
    {i q : V} (hi : i ∈ θ) (hq : q ∈ (forcingCodeP C) ‘ θ)
    {G : Set V} (hG : IsExternalForcingFilter
      ((forcingCodeP (kpair.π₁ (woodinIterationRec i))) ‘ i)
      ((forcingCodeR (kpair.π₁ (woodinIterationRec i))) ‘ i) G) :
    ((forcingCodeπ A) ‘ ⟨i, θ⟩ₖ) ‘ ((woodinSparseRealizationInverse θ) ‘ q) ∈ G ↔
      ((forcingCodeπ C) ‘ ⟨i, θ⟩ₖ) ‘ q ∈ woodinSparseGeneric i G := by
  have hm := function_value_mem (woodinSparseRealizationInverse_maps hΩ hAC hθ) hq
  have he := woodinSparseGeneric_quotient_projection_iff hΩ hAC hθ hi hm hG
  rw [woodinSparseRealizationMap_right_inverse hΩ hAC hθ hq] at he
  exact he.symm

end ZFVP
