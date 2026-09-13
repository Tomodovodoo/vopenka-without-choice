import ZFVP.ModelTheory.WoodinSparseQuotientInputs
import ZFVP.ModelTheory.ForcingRetractionModel

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem IsForcingSplitProjection.retraction_of_identity_section {P R Q S π E : V}
    (h : IsForcingSplitProjection P R Q S π E) (hE : ∀ p ∈ P, E ‘ p = p) :
    IsForcingRetraction P R Q S π := by
  refine ⟨h.projection.maps, ?_, ?_, h.projection.monotone, ?_, h.projection.lift⟩
  · intro p hp
    simpa only [hE p hp] using function_value_mem h.maps hp
  · intro p hp
    simpa only [hE p hp] using h.right_inverse p hp
  · intro q hq p hp
    simpa only [hE p hp] using h.below q hq p hp

variable {Ω θ i : V} [IsOrdinal θ]

theorem woodinSparseStage_retraction_to_row
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω)
    (hi : i ∈ θ) :
    IsForcingRetraction ((forcingCodeP (woodinSparseStageCode i)) ‘ i)
      ((forcingCodeR (woodinSparseStageCode i)) ‘ i)
      ((forcingCodeP (woodinSparseStageCode θ)) ‘ θ)
      ((forcingCodeR (woodinSparseStageCode θ)) ‘ θ)
      ((forcingCodeπ (woodinSparseStageCode θ)) ‘ ⟨i, θ⟩ₖ) := by
  have hi' : i ∈ succ θ := mem_succ_iff.mpr (Or.inr hi)
  rw [← (woodinSparseStage_old_row hi').1, ← (woodinSparseStage_old_row hi').2]
  exact ((woodinSparseStageCode_valid hΩ hAC hθ).system.splitProjection
    hi' (mem_succ_self θ) (IsOrdinal.toIsTransitive.transitive _ hi)).retraction_of_identity_section
      (fun p hp ↦ woodinSparseStageCode_section hΩ hAC hθ hi hp)

end ZFVP
