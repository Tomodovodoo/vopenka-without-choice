import ZFVP.ModelTheory.WoodinSparseRecursion

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem woodinSparseRecodingHistory_tables (θ : V) :
    IsIterationTable θ (woodinRecodingCarriers (woodinSparseRecodingHistory θ)) ∧
    IsIterationTable θ (woodinRecodingOrders (woodinSparseRecodingHistory θ)) ∧
    IsIterationTable θ (woodinRecodingMaps (woodinSparseRecodingHistory θ)) := by
  unfold woodinRecodingCarriers woodinRecodingOrders woodinRecodingMaps woodinSparseRecodingHistory
  simp only [domain_definableGraph]
  exact ⟨⟨inferInstance, domain_definableGraph _ _ _⟩,
    ⟨inferInstance, domain_definableGraph _ _ _⟩, ⟨inferInstance, domain_definableGraph _ _ _⟩⟩

theorem woodinSparseRecodingHistory_values {θ i : V} (hi : i ∈ θ) :
    (woodinRecodingCarriers (woodinSparseRecodingHistory θ)) ‘ i = kpair.π₁ (woodinSparseRecodingRec i) ∧
    (woodinRecodingOrders (woodinSparseRecodingHistory θ)) ‘ i = kpair.π₁ (kpair.π₂ (woodinSparseRecodingRec i)) ∧
    (woodinRecodingMaps (woodinSparseRecodingHistory θ)) ‘ i = kpair.π₂ (kpair.π₂ (woodinSparseRecodingRec i)) := by
  have hd : domain (woodinSparseRecodingHistory θ) = θ := domain_definableGraph _ _ _
  simp only [woodinRecodingCarriers, woodinRecodingOrders, woodinRecodingMaps,
    value_definableGraph _ _ _ (hd.symm ▸ hi), woodinSparseRecodingHistory_value hi, and_self]

theorem woodinSparseRecodingHistory_agrees {θ η i : V} (hi : i ∈ θ) (hi' : i ∈ η) :
    (woodinRecodingCarriers (woodinSparseRecodingHistory θ)) ‘ i = (woodinRecodingCarriers (woodinSparseRecodingHistory η)) ‘ i ∧
    (woodinRecodingOrders (woodinSparseRecodingHistory θ)) ‘ i = (woodinRecodingOrders (woodinSparseRecodingHistory η)) ‘ i ∧
    (woodinRecodingMaps (woodinSparseRecodingHistory θ)) ‘ i = (woodinRecodingMaps (woodinSparseRecodingHistory η)) ‘ i := by
  exact ⟨(woodinSparseRecodingHistory_values hi).1.trans (woodinSparseRecodingHistory_values hi').1.symm,
    (woodinSparseRecodingHistory_values hi).2.1.trans (woodinSparseRecodingHistory_values hi').2.1.symm,
    (woodinSparseRecodingHistory_values hi).2.2.trans (woodinSparseRecodingHistory_values hi').2.2.symm⟩

theorem woodinSparseRecodingHistory_family_of_rows {Ω θ : V} [IsOrdinal θ]
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω)
    (h : ∀ i ∈ θ, IsForcingIsomorphism ((forcingCodeP (woodinNormalizedStageCode i)) ‘ i)
      ((forcingCodeR (woodinNormalizedStageCode i)) ‘ i) (kpair.π₁ (woodinSparseRecodingRec i))
      (kpair.π₁ (kpair.π₂ (woodinSparseRecodingRec i))) (kpair.π₂ (kpair.π₂ (woodinSparseRecodingRec i)))) :
    ∀ i ∈ θ, IsForcingIsomorphism ((forcingCodeP (woodinNormalizedPrefixCode θ)) ‘ i)
      ((forcingCodeR (woodinNormalizedPrefixCode θ)) ‘ i)
      ((woodinRecodingCarriers (woodinSparseRecodingHistory θ)) ‘ i)
      ((woodinRecodingOrders (woodinSparseRecodingHistory θ)) ‘ i)
      ((woodinRecodingMaps (woodinSparseRecodingHistory θ)) ‘ i) := by
  intro i hi
  rw [(woodinNormalizedPrefix_row hΩ hAC hθ hi).1, (woodinNormalizedPrefix_row hΩ hAC hθ hi).2,
    (woodinSparseRecodingHistory_values hi).1, (woodinSparseRecodingHistory_values hi).2.1,
    (woodinSparseRecodingHistory_values hi).2.2]
  exact h i hi

end ZFVP
