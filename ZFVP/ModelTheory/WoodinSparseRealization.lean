import ZFVP.ModelTheory.WoodinSparseCanonicalLift
import ZFVP.ModelTheory.RetractionIsomorphism

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def woodinSparseRealizationMap (θ : V) : V :=
  compose (woodinNormalizationRec θ) (woodinSparseStageMap θ)

noncomputable def woodinSparseRealizationInverse (θ : V) : V := converseGraph (woodinSparseStageMap θ)

instance woodinSparseRealizationMap_definable : ℒₛₑₜ-function₁[V] woodinSparseRealizationMap := by
  unfold woodinSparseRealizationMap
  definability

instance woodinSparseRealizationInverse_definable : ℒₛₑₜ-function₁[V] woodinSparseRealizationInverse := by
  unfold woodinSparseRealizationInverse
  definability

variable {Ω θ : V} [IsOrdinal θ]
local notation "A" => kpair.π₁ (woodinIterationRec θ)
local notation "N" => woodinNormalizedStageCode θ
local notation "C" => woodinSparseStageCode θ

theorem woodinNormalizationHistory_family_le
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω) :
    IsForcingNormalizationFamily (succ θ) A (woodinNormalizationHistory (succ θ)) := by
  let := hΩ.inaccessible.1
  rcases IsOrdinal.subset_iff.mp hθ with rfl | hθ
  · exact woodinNormalizationHistory_endpoint_family hΩ hAC
  · exact woodinNormalizationHistory_family hΩ hAC θ hθ

theorem woodinIterationStageCode_valid_le
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω) :
    IsForcingIterationCode (succ θ) A := by
  let := hΩ.inaccessible.1
  rcases IsOrdinal.subset_iff.mp hθ with rfl | hθ
  · exact (woodinIteration_endpoint_valid hΩ hAC).1.code
  · exact ((woodinIterationExit hΩ hAC).2.1 θ hθ).1.code

theorem woodinNormalizationRec_retraction_le
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω) :
    IsForcingRetraction ((forcingCodeP N) ‘ θ) ((forcingCodeR N) ‘ θ)
      ((forcingCodeP A) ‘ θ) ((forcingCodeR A) ‘ θ) (woodinNormalizationRec θ) := by
  have h := (woodinNormalizationHistory_family_le hΩ hAC hθ).retraction θ (mem_succ_self θ)
  simpa only [woodinNormalizedStageCode, forcingNormalizedCode, forcingCodeP_code, forcingCodeR_code,
    forcingNormalizationOrders_value (mem_succ_self θ), forcingNormalizationCarriers_value (mem_succ_self θ),
    woodinNormalizationHistory_value (mem_succ_self θ)] using h

theorem woodinNormalizationRec_equivalent_le
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω)
    {p : V} (hp : p ∈ (forcingCodeP A) ‘ θ) :
    ⟨(woodinNormalizationRec θ) ‘ p, p⟩ₖ ∈ (forcingCodeR A) ‘ θ ∧
      ⟨p, (woodinNormalizationRec θ) ‘ p⟩ₖ ∈ (forcingCodeR A) ‘ θ := by
  simpa only [woodinNormalizationHistory_value (mem_succ_self θ)] using
    (woodinNormalizationHistory_family_le hΩ hAC hθ).equivalent θ (mem_succ_self θ) p hp

theorem woodinSparseRealizationMap_projection
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω) :
    IsForcingProjection ((forcingCodeP C) ‘ θ) ((forcingCodeR C) ‘ θ)
      ((forcingCodeP A) ‘ θ) ((forcingCodeR A) ‘ θ) (woodinSparseRealizationMap θ) :=
  (woodinNormalizationRec_retraction_le hΩ hAC hθ).isomorphism_projection (woodinSparseStageMap_isomorphism hΩ hAC hθ)

theorem woodinSparseRealizationMap_value
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω)
    {p : V} (hp : p ∈ (forcingCodeP A) ‘ θ) :
    (woodinSparseRealizationMap θ) ‘ p = (woodinSparseStageMap θ) ‘ ((woodinNormalizationRec θ) ‘ p) :=
  value_compose_of_mem_function (woodinNormalizationRec_retraction_le hΩ hAC hθ).maps
    (woodinSparseStageMap_isomorphism hΩ hAC hθ).1 hp

theorem woodinSparseRealizationInverse_maps
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω) :
    woodinSparseRealizationInverse θ ∈ ((forcingCodeP A) ‘ θ) ^ ((forcingCodeP C) ‘ θ) :=
  mem_function_of_mem_function_of_subset (woodinSparseStageMap_isomorphism hΩ hAC hθ).inverse_maps
    (woodinNormalizationRec_retraction_le hΩ hAC hθ).inclusion

theorem woodinSparseRealizationMap_right_inverse
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω)
    {q : V} (hq : q ∈ (forcingCodeP C) ‘ θ) :
    (woodinSparseRealizationMap θ) ‘ ((woodinSparseRealizationInverse θ) ‘ q) = q :=
  (woodinNormalizationRec_retraction_le hΩ hAC hθ).isomorphism_right_inverse
    (woodinSparseStageMap_isomorphism hΩ hAC hθ) hq

theorem woodinSparseRealizationMap_left_inverse
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω)
    {p : V} (hp : p ∈ (forcingCodeP A) ‘ θ) :
    (woodinSparseRealizationInverse θ) ‘ ((woodinSparseRealizationMap θ) ‘ p) = (woodinNormalizationRec θ) ‘ p :=
  (woodinNormalizationRec_retraction_le hΩ hAC hθ).isomorphism_left_inverse
    (woodinSparseStageMap_isomorphism hΩ hAC hθ) hp

theorem woodinSparseRealizationMap_left_equivalent
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω)
    {p : V} (hp : p ∈ (forcingCodeP A) ‘ θ) :
    ⟨(woodinSparseRealizationInverse θ) ‘ ((woodinSparseRealizationMap θ) ‘ p), p⟩ₖ ∈ (forcingCodeR A) ‘ θ ∧
    ⟨p, (woodinSparseRealizationInverse θ) ‘ ((woodinSparseRealizationMap θ) ‘ p)⟩ₖ ∈ (forcingCodeR A) ‘ θ := by
  rw [woodinSparseRealizationMap_left_inverse hΩ hAC hθ hp]
  exact woodinNormalizationRec_equivalent_le hΩ hAC hθ hp

theorem woodinSparseRealizationMap_order_iff
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω)
    {p q : V} (hp : p ∈ (forcingCodeP A) ‘ θ) (hq : q ∈ (forcingCodeP A) ‘ θ) :
    ⟨p, q⟩ₖ ∈ (forcingCodeR A) ‘ θ ↔
      ⟨(woodinSparseRealizationMap θ) ‘ p, (woodinSparseRealizationMap θ) ‘ q⟩ₖ ∈ (forcingCodeR C) ‘ θ :=
  (woodinNormalizationRec_retraction_le hΩ hAC hθ).isomorphism_order_iff
    (woodinSparseStageMap_isomorphism hΩ hAC hθ)
    ((woodinIterationStageCode_valid_le hΩ hAC hθ).system.order.preorder θ (mem_succ_self θ))
    (fun _ hp ↦ (woodinNormalizationRec_equivalent_le hΩ hAC hθ hp).1) hp hq

theorem woodinSparseRealizationMap_forcingFormula_iff
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω)
    {k : ℕ} (φ : SetTheorySemisentence k) (v : Fin k → V)
    (hv : ∀ i, IsForcingName ((forcingCodeP A) ‘ θ) (v i))
    {p : V} (hp : p ∈ (forcingCodeP A) ‘ θ) :
    p ∈ forcingFormula ((forcingCodeP A) ‘ θ) ((forcingCodeR A) ‘ θ) φ (standardTuple v) ↔
      (woodinSparseRealizationMap θ) ‘ p ∈ forcingFormula ((forcingCodeP C) ‘ θ) ((forcingCodeR C) ‘ θ)
        φ (standardTuple (fun i ↦ nameAction (woodinSparseRealizationMap θ) (v i))) :=
  (woodinNormalizationRec_retraction_le hΩ hAC hθ).isomorphism_forcingFormula_iff
    (woodinSparseStageMap_isomorphism hΩ hAC hθ)
    ((woodinIterationStageCode_valid_le hΩ hAC hθ).system.order.preorder θ (mem_succ_self θ))
    ((woodinNormalizedStage_through_endpoint hΩ hAC hθ).1.system.order.preorder θ (mem_succ_self θ))
    ((woodinSparseStageCode_valid hΩ hAC hθ).system.order.preorder θ (mem_succ_self θ))
    (fun _ hp ↦ woodinNormalizationRec_equivalent_le hΩ hAC hθ hp) φ v hv hp

end ZFVP
