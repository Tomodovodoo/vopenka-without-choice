import ZFVP.ModelTheory.WoodinSparseCodeLaws
import ZFVP.ModelTheory.WoodinSparseEndpoint

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
noncomputable def woodinSparseStageCode (θ : V) : V :=
  forcingRecodedCode (succ θ) (woodinNormalizedStageCode θ)
    (woodinRecodingCarriers (woodinSparseRecodingHistory (succ θ)))
    (woodinRecodingOrders (woodinSparseRecodingHistory (succ θ)))
    (woodinRecodingMaps (woodinSparseRecodingHistory (succ θ)))

instance woodinSparseStageCode_definable : ℒₛₑₜ-function₁[V] woodinSparseStageCode := by
  unfold woodinSparseStageCode
  apply Language.DefinableFunction₅.comp <;> definability

theorem woodinSparseStageCode_endpoint_family {Ω : V}
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) :
    ∀ i ∈ succ Ω, IsForcingIsomorphism ((forcingCodeP (woodinNormalizedStageCode Ω)) ‘ i)
      ((forcingCodeR (woodinNormalizedStageCode Ω)) ‘ i)
      ((woodinRecodingCarriers (woodinSparseRecodingHistory (succ Ω))) ‘ i)
      ((woodinRecodingOrders (woodinSparseRecodingHistory (succ Ω))) ‘ i)
      ((woodinRecodingMaps (woodinSparseRecodingHistory (succ Ω))) ‘ i) := by
  let := hΩ.inaccessible.1
  have he := woodinNormalizedStageCode_endpoint_extends hΩ hAC
  have hs := woodinNormalizedPrefixCode_valid hΩ hAC (subset_refl Ω)
  have hz := woodinNormalizedStageCode_endpoint_valid hΩ hAC
  intro i hi
  rw [(woodinSparseRecodingHistory_values hi).1, (woodinSparseRecodingHistory_values hi).2.1,
    (woodinSparseRecodingHistory_values hi).2.2]
  rcases mem_succ_iff.mp hi with rfl | hi
  · exact (woodinSparseRecodingRec_endpoint_correct hΩ hAC).1.1
  · rw [← hs.tableP.value_of_subset hz.tableP he.subP hi,
      ← hs.tableR.value_of_subset hz.tableR he.subR hi,
      (woodinNormalizedPrefix_row hΩ hAC (subset_refl Ω) hi).1,
      (woodinNormalizedPrefix_row hΩ hAC (subset_refl Ω) hi).2]
    exact (woodinSparseRecodingRec_correct hΩ hAC i hi).1.1

theorem woodinSparseStageCode_endpoint_valid {Ω : V}
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) :
    IsForcingIterationCode (succ Ω) (woodinSparseStageCode Ω) := by
  let := hΩ.inaccessible.1
  apply forcingRecoded_code (woodinNormalizedStageCode_endpoint_valid hΩ hAC)
    (woodinSparseStageCode_endpoint_family hΩ hAC) ?_
    (woodinSparseRecodingHistory_tables (succ Ω)).1 (woodinSparseRecodingHistory_tables (succ Ω)).2.1
  intro i hi
  rw [(woodinSparseRecodingHistory_values hi).1, (woodinSparseRecodingHistory_values hi).2.1]
  rcases mem_succ_iff.mp hi with rfl | hi
  · exact (woodinSparseRecodingRec_endpoint_correct hΩ hAC).1.2.1
  · exact (woodinSparseRecodingRec_correct hΩ hAC i hi).1.2.1

theorem woodinSparseStageCode_endpoint_extends {Ω : V}
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) :
    ForcingCodeExtends (woodinSparsePrefixCode Ω) (woodinSparseStageCode Ω) := by
  let := hΩ.inaccessible.1
  have hsub : Ω ⊆ succ Ω := fun _ hi ↦ mem_succ_iff.mpr (Or.inr hi)
  exact forcingRecoded_extends (woodinNormalizedPrefixCode_valid hΩ hAC (subset_refl Ω))
    (woodinNormalizedStageCode_endpoint_valid hΩ hAC) (woodinNormalizedStageCode_endpoint_extends hΩ hAC) hsub
    (fun i hi ↦ (woodinSparseRecodingHistory_agrees hi (hsub i hi)).1)
    (fun i hi ↦ (woodinSparseRecodingHistory_agrees hi (hsub i hi)).2.1)
    (fun i hi ↦ (woodinSparseRecodingHistory_agrees hi (hsub i hi)).2.2)
    (woodinSparsePrefixCode_valid hΩ hAC (subset_refl Ω)) (woodinSparseStageCode_endpoint_valid hΩ hAC)

theorem woodinSparseStageCode_eq_prefix {Ω θ : V} [IsOrdinal θ]
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ∈ Ω) :
    woodinSparseStageCode θ = woodinSparsePrefixCode (succ θ) := by
  unfold woodinSparseStageCode woodinSparsePrefixCode
  rw [woodinNormalizedPrefix_successor hΩ hAC hθ]

theorem woodinSparseRecodingRec_correct_le {Ω θ : V} [IsOrdinal θ]
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω) :
    IsWoodinSparseRow θ (woodinSparseRecodingRec θ) := by
  let := hΩ.inaccessible.1
  rcases IsOrdinal.subset_iff.mp hθ with rfl | hθ
  · exact woodinSparseRecodingRec_endpoint_correct hΩ hAC
  · exact woodinSparseRecodingRec_correct hΩ hAC θ hθ

theorem woodinSparseStageCode_family {Ω θ : V} [IsOrdinal θ]
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω) :
    ∀ i ∈ succ θ, IsForcingIsomorphism ((forcingCodeP (woodinNormalizedStageCode θ)) ‘ i)
      ((forcingCodeR (woodinNormalizedStageCode θ)) ‘ i)
      ((woodinRecodingCarriers (woodinSparseRecodingHistory (succ θ))) ‘ i)
      ((woodinRecodingOrders (woodinSparseRecodingHistory (succ θ))) ‘ i)
      ((woodinRecodingMaps (woodinSparseRecodingHistory (succ θ))) ‘ i) := by
  let := hΩ.inaccessible.1
  rcases IsOrdinal.subset_iff.mp hθ with rfl | hθ
  · exact woodinSparseStageCode_endpoint_family hΩ hAC
  · rw [← woodinNormalizedPrefix_successor hΩ hAC hθ]
    apply woodinSparsePrefix_family hΩ hAC
    intro i hi
    rcases mem_succ_iff.mp hi with rfl | hi
    · exact hθ
    · exact IsOrdinal.toIsTransitive.mem_trans hi hθ

theorem woodinSparseStageCode_valid {Ω θ : V} [IsOrdinal θ]
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω) :
    IsForcingIterationCode (succ θ) (woodinSparseStageCode θ) := by
  let := hΩ.inaccessible.1
  rcases IsOrdinal.subset_iff.mp hθ with rfl | hθ
  · exact woodinSparseStageCode_endpoint_valid hΩ hAC
  · rw [woodinSparseStageCode_eq_prefix hΩ hAC hθ]
    apply woodinSparsePrefixCode_valid hΩ hAC
    intro i hi
    rcases mem_succ_iff.mp hi with rfl | hi
    · exact hθ
    · exact IsOrdinal.toIsTransitive.mem_trans hi hθ

theorem woodinSparseStageCode_extends {Ω θ : V} [IsOrdinal θ]
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω) :
    ForcingCodeExtends (woodinSparsePrefixCode θ) (woodinSparseStageCode θ) := by
  let := hΩ.inaccessible.1
  rcases IsOrdinal.subset_iff.mp hθ with rfl | hθ
  · exact woodinSparseStageCode_endpoint_extends hΩ hAC
  · rw [woodinSparseStageCode_eq_prefix hΩ hAC hθ]
    apply woodinSparsePrefixCode_extends hΩ hAC
    · intro i hi
      rcases mem_succ_iff.mp hi with rfl | hi
      · exact hθ
      · exact IsOrdinal.toIsTransitive.mem_trans hi hθ
    · exact fun i hi ↦ mem_succ_iff.mpr (Or.inr hi)

end ZFVP
