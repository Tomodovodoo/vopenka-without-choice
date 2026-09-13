import ZFVP.ModelTheory.WoodinRecodingConstruction

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def woodinRecodedPrefixCode (θ : V) : V :=
  forcingRecodedCode θ (woodinNormalizedPrefixCode θ)
    (woodinRecodingCarriers (woodinRecodingHistory θ))
    (woodinRecodingOrders (woodinRecodingHistory θ))
    (woodinRecodingMaps (woodinRecodingHistory θ))

instance woodinRecodedPrefixCode_definable : ℒₛₑₜ-function₁[V] woodinRecodedPrefixCode := by
  unfold woodinRecodedPrefixCode
  apply Language.DefinableFunction₅.comp <;> definability

theorem woodinRecodedPrefix_family {Ω θ : V} [IsOrdinal θ]
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω) :
    ∀ i ∈ θ, IsForcingIsomorphism ((forcingCodeP (woodinNormalizedPrefixCode θ)) ‘ i)
      ((forcingCodeR (woodinNormalizedPrefixCode θ)) ‘ i)
      ((woodinRecodingCarriers (woodinRecodingHistory θ)) ‘ i)
      ((woodinRecodingOrders (woodinRecodingHistory θ)) ‘ i)
      ((woodinRecodingMaps (woodinRecodingHistory θ)) ‘ i) :=
  woodinRecodingHistory_family_of_rows hΩ hAC hθ
    (fun i hi ↦ (woodinRecodingRec_correct hΩ hAC i (hθ i hi)).1)

theorem woodinRecodedPrefix_preorders {Ω θ : V}
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω) :
    ∀ i ∈ θ, IsForcingPreorder ((woodinRecodingCarriers (woodinRecodingHistory θ)) ‘ i)
      ((woodinRecodingOrders (woodinRecodingHistory θ)) ‘ i) := by
  intro i hi
  rw [(woodinRecodingHistory_values hi).1, (woodinRecodingHistory_values hi).2.1]
  exact (woodinRecodingRec_correct hΩ hAC i (hθ i hi)).2.1

theorem woodinRecodedPrefixCode_valid {Ω θ : V} [IsOrdinal θ]
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω) :
    IsForcingIterationCode θ (woodinRecodedPrefixCode θ) :=
  forcingRecoded_code (woodinNormalizedPrefixCode_valid hΩ hAC hθ)
    (woodinRecodedPrefix_family hΩ hAC hθ) (woodinRecodedPrefix_preorders hΩ hAC hθ)
    (woodinRecodingHistory_tables θ).1 (woodinRecodingHistory_tables θ).2.1

theorem woodinRecodedPrefixCode_small {Ω θ i ξ : V}
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω) (hi : i ∈ θ)
    (hξ : IsChoicelessInaccessible ξ) (hcard : (kpair.π₂ (woodinIterationRec i)) ‘ i ∈ ξ) :
    (forcingCodeP (woodinRecodedPrefixCode θ)) ‘ i ∈ hierarchy ξ := by
  simp only [woodinRecodedPrefixCode, forcingRecodedCode, forcingCodeP_code,
    (woodinRecodingHistory_values hi).1]
  exact (woodinRecodingRec_correct hΩ hAC i (hθ i hi)).2.2 ξ hξ hcard

theorem woodinRecodedPrefixCode_extends {Ω θ η : V} [IsOrdinal θ] [IsOrdinal η]
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hη : η ⊆ Ω) (hθη : θ ⊆ η) :
    ForcingCodeExtends (woodinRecodedPrefixCode θ) (woodinRecodedPrefixCode η) := by
  have hθ := subset_trans hθη hη
  exact forcingRecoded_extends (woodinNormalizedPrefixCode_valid hΩ hAC hθ)
    (woodinNormalizedPrefixCode_valid hΩ hAC hη) (woodinNormalizedPrefix_extends hΩ hAC hη hθη) hθη
    (fun i hi ↦ (woodinRecodingHistory_agrees hi (hθη i hi)).1)
    (fun i hi ↦ (woodinRecodingHistory_agrees hi (hθη i hi)).2.1)
    (fun i hi ↦ (woodinRecodingHistory_agrees hi (hθη i hi)).2.2)
    (woodinRecodedPrefixCode_valid hΩ hAC hθ) (woodinRecodedPrefixCode_valid hΩ hAC hη)

theorem woodinRecodedPrefixCode_restrictions {Ω θ η : V} [IsOrdinal θ] [IsOrdinal η]
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hη : η ⊆ Ω) (hθη : θ ⊆ η) :
    (forcingCodeP (woodinRecodedPrefixCode η)) ↾ θ = forcingCodeP (woodinRecodedPrefixCode θ) ∧
    (forcingCodeR (woodinRecodedPrefixCode η)) ↾ θ = forcingCodeR (woodinRecodedPrefixCode θ) ∧
    (forcingCodeπ (woodinRecodedPrefixCode η)) ↾ (θ ×ˢ θ) = forcingCodeπ (woodinRecodedPrefixCode θ) ∧
    (forcingCodeE (woodinRecodedPrefixCode η)) ↾ (θ ×ˢ θ) = forcingCodeE (woodinRecodedPrefixCode θ) ∧
    (forcingCodeL (woodinRecodedPrefixCode η)) ↾ (θ ×ˢ θ) = forcingCodeL (woodinRecodedPrefixCode θ) ∧
    (forcingCodet (woodinRecodedPrefixCode η)) ↾ θ = forcingCodet (woodinRecodedPrefixCode θ) :=
  (woodinRecodedPrefixCode_extends hΩ hAC hη hθη).restrictions
    (woodinRecodedPrefixCode_valid hΩ hAC (subset_trans hθη hη))
    (woodinRecodedPrefixCode_valid hΩ hAC hη) hθη

end ZFVP
