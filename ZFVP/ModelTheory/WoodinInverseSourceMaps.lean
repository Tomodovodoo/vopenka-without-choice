import ZFVP.ModelTheory.WoodinNormalizationInverseCoherence

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable {θ s K : V}
local notation "C" => woodinInverseSourceCode θ s K
local notation "P" => forcingInverseCodePoset θ s

theorem woodinInverseSourceCode_first {z : V} (hz : z ∈ (forcingCodeP C) ‘ θ) :
    kpair.π₁ z ∈ P := by
  rw [woodinInverseSourceCode_poset] at hz
  simpa only [twoStepProjection_value hz] using function_value_mem (twoStepProjection_maps _ _ _ _) hz

theorem woodinInverseSourceCode_projection {i z : V} (hi : i ∈ θ)
    (hz : z ∈ (forcingCodeP C) ‘ θ) :
    ((forcingCodeπ C) ‘ ⟨i, θ⟩ₖ) ‘ z = (kpair.π₁ z) ‘ i := by
  have hp := woodinInverseSourceCode_first hz
  rw [woodinInverseSourceCode_poset] at hz
  simp only [woodinInverseSourceCode_twoStepColumn, forcingTwoStepColumnCode,
    forcingIterationCodeNext, forcingCodeπ_code, forcingMatrixNext_column hi,
    forcingComposeProjectionColumn_value hi, forcingLimitProjectionColumn_value hi]
  simp only [forcingInverseCodePoset] at hz hp ⊢
  rw [value_compose_of_mem_function (twoStepProjection_maps _ _ _ _) (forcingThreadCoordinate_maps hi) hz,
    twoStepProjection_value hz, forcingThreadCoordinate_value hp]

theorem woodinInverseSourceCode_section [IsOrdinal θ] (hs : IsForcingIterationCode θ s)
    (h0 : ∅ ∈ θ) {i p : V} (hi : i ∈ θ) (hp : p ∈ (forcingCodeP s) ‘ i) :
    ((forcingCodeE C) ‘ ⟨i, θ⟩ₖ) ‘ p =
      ⟨forcingSectionThread θ (forcingCodeπ s) (forcingCodeE s) i p, ∅⟩ₖ := by
  have col := hs.system.inverseColumn h0 hs.subset_universe
  have hm : (forcingLimitSectionColumn θ (forcingCodeP s) (forcingCodeπ s) (forcingCodeE s)) ‘ i ∈
      P ^ ((forcingCodeP s) ‘ i) := col.functions.sectionMap i hi
  have hf : IsFunction (twoStepSection P (∅ : V)) := by
    unfold twoStepSection
    infer_instance
  let := hf
  have hsec : twoStepSection P (∅ : V) ∈ range (twoStepSection P (∅ : V)) ^ P := by
    simpa only [twoStepSection, domain_definableGraph] using IsFunction.mem_function (twoStepSection P (∅ : V))
  simp only [woodinInverseSourceCode_twoStepColumn, forcingTwoStepColumnCode, forcingIterationCodeNext,
    forcingCodeE_code, forcingMatrixNext_column hi, forcingComposeSectionColumn_value hi]
  rw [value_compose_of_mem_function hm hsec hp,
    twoStepSection_value (function_value_mem hm hp), forcingLimitSectionColumn_value hi,
    forcingThreadSection_value hp]

theorem woodinInverseSourceCode_lift {i z p : V} (hi : i ∈ θ)
    (hz : z ∈ (forcingCodeP C) ‘ θ) (hp : p ∈ (forcingCodeP s) ‘ i) :
    ((forcingCodeL C) ‘ ⟨i, θ⟩ₖ) ‘ ⟨z, p⟩ₖ =
      ⟨forcingThreadSplice θ (forcingCodeπ s) (forcingCodeL s) (kpair.π₁ z) i p, kpair.π₂ z⟩ₖ := by
  have hf := woodinInverseSourceCode_first hz
  rw [woodinInverseSourceCode_poset] at hz
  simp only [woodinInverseSourceCode_twoStepColumn, forcingTwoStepColumnCode, forcingIterationCodeNext,
    forcingCodeL_code, forcingMatrixNext_column hi]
  rw [forcingTwoStepLiftColumn_value hi hz hp]
  simp only [successorForcingLiftValue, twoStepStronger,
    forcingLimitLiftColumn_value hi, forcingLimitLift_value hf hp]

end ZFVP
