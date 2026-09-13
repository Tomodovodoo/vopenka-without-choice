import ZFVP.ModelTheory.WoodinSparseConstruction

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def woodinSparsePrefixCode (θ : V) : V :=
  forcingRecodedCode θ (woodinNormalizedPrefixCode θ)
    (woodinRecodingCarriers (woodinSparseRecodingHistory θ))
    (woodinRecodingOrders (woodinSparseRecodingHistory θ))
    (woodinRecodingMaps (woodinSparseRecodingHistory θ))

instance woodinSparsePrefixCode_definable : ℒₛₑₜ-function₁[V] woodinSparsePrefixCode := by
  unfold woodinSparsePrefixCode
  apply Language.DefinableFunction₅.comp <;> definability

theorem woodinSparsePrefix_family {Ω θ : V} [IsOrdinal θ]
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω) :
    ∀ i ∈ θ, IsForcingIsomorphism ((forcingCodeP (woodinNormalizedPrefixCode θ)) ‘ i)
      ((forcingCodeR (woodinNormalizedPrefixCode θ)) ‘ i)
      ((woodinRecodingCarriers (woodinSparseRecodingHistory θ)) ‘ i)
      ((woodinRecodingOrders (woodinSparseRecodingHistory θ)) ‘ i)
      ((woodinRecodingMaps (woodinSparseRecodingHistory θ)) ‘ i) :=
  woodinSparseRecodingHistory_family_of_rows hΩ hAC hθ
    (fun i hi ↦ (woodinSparseRecodingRec_correct hΩ hAC i (hθ i hi)).1.1)

theorem woodinSparsePrefix_preorders {Ω θ : V}
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω) :
    ∀ i ∈ θ, IsForcingPreorder ((woodinRecodingCarriers (woodinSparseRecodingHistory θ)) ‘ i)
      ((woodinRecodingOrders (woodinSparseRecodingHistory θ)) ‘ i) := by
  intro i hi
  rw [(woodinSparseRecodingHistory_values hi).1, (woodinSparseRecodingHistory_values hi).2.1]
  exact (woodinSparseRecodingRec_correct hΩ hAC i (hθ i hi)).1.2.1

theorem woodinSparsePrefixCode_valid {Ω θ : V} [IsOrdinal θ]
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω) :
    IsForcingIterationCode θ (woodinSparsePrefixCode θ) :=
  forcingRecoded_code (woodinNormalizedPrefixCode_valid hΩ hAC hθ)
    (woodinSparsePrefix_family hΩ hAC hθ) (woodinSparsePrefix_preorders hΩ hAC hθ)
    (woodinSparseRecodingHistory_tables θ).1 (woodinSparseRecodingHistory_tables θ).2.1

theorem woodinSparsePrefixCode_small {Ω θ i ξ : V}
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω) (hi : i ∈ θ)
    (hξ : IsChoicelessInaccessible ξ) (hcard : (kpair.π₂ (woodinIterationRec i)) ‘ i ∈ ξ) :
    (forcingCodeP (woodinSparsePrefixCode θ)) ‘ i ∈ hierarchy ξ := by
  simp only [woodinSparsePrefixCode, forcingRecodedCode, forcingCodeP_code,
    (woodinSparseRecodingHistory_values hi).1]
  exact (woodinSparseRecodingRec_correct hΩ hAC i (hθ i hi)).1.2.2 ξ hξ hcard

theorem woodinSparsePrefixCode_extends {Ω θ η : V} [IsOrdinal θ] [IsOrdinal η]
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hη : η ⊆ Ω) (hθη : θ ⊆ η) :
    ForcingCodeExtends (woodinSparsePrefixCode θ) (woodinSparsePrefixCode η) := by
  have hθ := subset_trans hθη hη
  exact forcingRecoded_extends (woodinNormalizedPrefixCode_valid hΩ hAC hθ)
    (woodinNormalizedPrefixCode_valid hΩ hAC hη) (woodinNormalizedPrefix_extends hΩ hAC hη hθη) hθη
    (fun i hi ↦ (woodinSparseRecodingHistory_agrees hi (hθη i hi)).1)
    (fun i hi ↦ (woodinSparseRecodingHistory_agrees hi (hθη i hi)).2.1)
    (fun i hi ↦ (woodinSparseRecodingHistory_agrees hi (hθη i hi)).2.2)
    (woodinSparsePrefixCode_valid hΩ hAC hθ) (woodinSparsePrefixCode_valid hΩ hAC hη)

theorem woodinSparsePrefixCode_restrictions {Ω θ η : V} [IsOrdinal θ] [IsOrdinal η]
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hη : η ⊆ Ω) (hθη : θ ⊆ η) :
    (forcingCodeP (woodinSparsePrefixCode η)) ↾ θ = forcingCodeP (woodinSparsePrefixCode θ) ∧
    (forcingCodeR (woodinSparsePrefixCode η)) ↾ θ = forcingCodeR (woodinSparsePrefixCode θ) ∧
    (forcingCodeπ (woodinSparsePrefixCode η)) ↾ (θ ×ˢ θ) = forcingCodeπ (woodinSparsePrefixCode θ) ∧
    (forcingCodeE (woodinSparsePrefixCode η)) ↾ (θ ×ˢ θ) = forcingCodeE (woodinSparsePrefixCode θ) ∧
    (forcingCodeL (woodinSparsePrefixCode η)) ↾ (θ ×ˢ θ) = forcingCodeL (woodinSparsePrefixCode θ) ∧
    (forcingCodet (woodinSparsePrefixCode η)) ↾ θ = forcingCodet (woodinSparsePrefixCode θ) :=
  (woodinSparsePrefixCode_extends hΩ hAC hη hθη).restrictions
    (woodinSparsePrefixCode_valid hΩ hAC (subset_trans hθη hη))
    (woodinSparsePrefixCode_valid hΩ hAC hη) hθη

end ZFVP
