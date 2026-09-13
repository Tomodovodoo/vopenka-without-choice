import ZFVP.ModelTheory.WoodinSparseStageCode

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable {Ω θ : V} [IsOrdinal θ]
variable (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω)
local notation "C" => woodinSparseStageCode θ
local notation "N" => woodinNormalizedStageCode θ
local notation "m" => woodinRecodingMaps (woodinSparseRecodingHistory (succ θ))

include hΩ hAC hθ in
theorem woodinSparseStageCode_sparse {p : V} (hp : p ∈ (forcingCodeP C) ‘ θ) :
    IsSparseFunctionOn (succ (woodinSourceIndex θ)) p := by
  simp only [woodinSparseStageCode, forcingRecodedCode, forcingCodeP_code,
    (woodinSparseRecodingHistory_values (mem_succ_self θ)).1] at hp
  exact (woodinSparseRecodingRec_correct_le hΩ hAC hθ).2.1 p hp

include hΩ hAC hθ in
theorem woodinSparseStageCode_top : (forcingCodet C) ‘ θ = ∅ := by
  simp only [woodinSparseStageCode, forcingRecodedCode, forcingCodet_code,
    forcingRecodedTops_value (mem_succ_self θ),
    (woodinSparseRecodingHistory_values (mem_succ_self θ)).2.2]
  exact (woodinSparseRecodingRec_correct_le hΩ hAC hθ).2.2.1

include hΩ hAC hθ in
theorem woodinSparseStageCode_projection {i p : V} (hi : i ∈ θ)
    (hp : p ∈ (forcingCodeP C) ‘ θ) :
    ((forcingCodeπ C) ‘ ⟨i, θ⟩ₖ) ‘ p = p ↾ (succ (woodinSourceIndex i)) := by
  have hm := woodinSparseStageCode_family hΩ hAC hθ
  have hs : IsForcingIterationCode (succ θ) N := by
    let := hΩ.inaccessible.1
    rcases IsOrdinal.subset_iff.mp hθ with rfl | hθ
    · exact woodinNormalizedStageCode_endpoint_valid hΩ hAC
    · exact woodinNormalizedStageCode_valid hΩ hAC hθ
  have hi' : i ∈ succ θ := mem_succ_iff.mpr (Or.inr hi)
  have ht := mem_succ_self θ
  simp only [woodinSparseStageCode, forcingRecodedCode, forcingCodeP_code] at hp
  obtain ⟨z, hz, rfl⟩ := (hm θ ht).surjective p hp
  simp only [woodinSparseStageCode, forcingRecodedCode, forcingCodeπ_code]
  rw [forcingRecodedProjections_image hs hm hi' ht (IsOrdinal.toIsTransitive.transitive _ hi) hz,
    (woodinSparseRecodingHistory_values hi').2.2, (woodinSparseRecodingHistory_values ht).2.2]
  exact ((woodinSparseRecodingRec_correct_le hΩ hAC hθ).2.2.2.1 i hi z hz).symm

include hΩ hAC hθ in
theorem woodinSparseStageCode_section {i p : V} (hi : i ∈ θ)
    (hp : p ∈ (forcingCodeP C) ‘ i) :
    ((forcingCodeE C) ‘ ⟨i, θ⟩ₖ) ‘ p = p := by
  have hm := woodinSparseStageCode_family hΩ hAC hθ
  have hs : IsForcingIterationCode (succ θ) N := by
    let := hΩ.inaccessible.1
    rcases IsOrdinal.subset_iff.mp hθ with rfl | hθ
    · exact woodinNormalizedStageCode_endpoint_valid hΩ hAC
    · exact woodinNormalizedStageCode_valid hΩ hAC hθ
  have hi' : i ∈ succ θ := mem_succ_iff.mpr (Or.inr hi)
  have ht := mem_succ_self θ
  simp only [woodinSparseStageCode, forcingRecodedCode, forcingCodeP_code] at hp
  obtain ⟨z, hz, rfl⟩ := (hm i hi').surjective p hp
  simp only [woodinSparseStageCode, forcingRecodedCode, forcingCodeE_code]
  rw [forcingRecodedSections_image hs hm hi' ht (IsOrdinal.toIsTransitive.transitive _ hi) hz,
    (woodinSparseRecodingHistory_values hi').2.2, (woodinSparseRecodingHistory_values ht).2.2]
  exact (woodinSparseRecodingRec_correct_le hΩ hAC hθ).2.2.2.2 i hi z hz

include hΩ hAC hθ in
theorem woodinSparseStageCode_small {ξ : V} (hξ : IsChoicelessInaccessible ξ)
    (hcard : (kpair.π₂ (woodinIterationRec θ)) ‘ θ ∈ ξ) :
    (forcingCodeP C) ‘ θ ∈ hierarchy ξ := by
  simp only [woodinSparseStageCode, forcingRecodedCode, forcingCodeP_code,
    (woodinSparseRecodingHistory_values (mem_succ_self θ)).1]
  exact (woodinSparseRecodingRec_correct_le hΩ hAC hθ).1.2.2 ξ hξ hcard

end ZFVP
