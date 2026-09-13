import ZFVP.ModelTheory.WoodinSparseFixedPointInclusion
import ZFVP.ModelTheory.ForcingContextCongruence

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable {Ω : V} [IsOrdinal Ω]

theorem woodinSparseEndpoint_raw_generic_presentation
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (A : ForcingContext V)
    (hP : A.P = (forcingCodeP (woodinSparseStageCode Ω)) ‘ Ω)
    (hR : A.R = (forcingCodeR (woodinSparseStageCode Ω)) ‘ Ω)
    (hone : A.one = ∅) :
    ∃ G : Set V, ∃ hG : IsExternalForcingGeneric
      ((forcingCodeP (kpair.π₁ (woodinIterationRec Ω))) ‘ Ω)
      ((forcingCodeR (kpair.π₁ (woodinIterationRec Ω))) ‘ Ω) G,
      woodinSparseGenericContext hΩ hAC (subset_refl Ω) hG = A := by
  have hA : IsExternalForcingGeneric ((forcingCodeP (woodinSparseStageCode Ω)) ‘ Ω)
      ((forcingCodeR (woodinSparseStageCode Ω)) ‘ Ω) A.G := by
    simpa only [← hP, ← hR] using A.generic
  let G := forcingProjectionPreimage ((forcingCodeP (kpair.π₁ (woodinIterationRec Ω))) ‘ Ω)
    (woodinSparseRealizationMap Ω) A.G
  have hG : IsExternalForcingGeneric
      ((forcingCodeP (kpair.π₁ (woodinIterationRec Ω))) ‘ Ω)
      ((forcingCodeR (kpair.π₁ (woodinIterationRec Ω))) ‘ Ω) G :=
    woodinSparseGeneric_preimage_generic hΩ hAC (subset_refl Ω) hA
  refine ⟨G, hG, ?_⟩
  apply ForcingContext.eq_of_data_eq
  · exact hP.symm
  · exact hR.symm
  · exact (woodinSparseGenericContext_top hΩ hAC (subset_refl Ω) hG).trans hone.symm
  · rw [woodinSparseGenericContext_generic]
    exact woodinSparseGeneric_image_preimage hΩ hAC (subset_refl Ω) hA.1

end ZFVP
