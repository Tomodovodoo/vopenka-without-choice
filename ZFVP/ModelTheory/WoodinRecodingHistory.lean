import ZFVP.ModelTheory.WoodinRecodingRecursion

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem woodinRecodingHistory_tables (θ : V) :
    IsIterationTable θ (woodinRecodingCarriers (woodinRecodingHistory θ)) ∧
    IsIterationTable θ (woodinRecodingOrders (woodinRecodingHistory θ)) ∧
    IsIterationTable θ (woodinRecodingMaps (woodinRecodingHistory θ)) := by
  unfold woodinRecodingCarriers woodinRecodingOrders woodinRecodingMaps woodinRecodingHistory
  simp only [domain_definableGraph]
  exact ⟨⟨inferInstance, domain_definableGraph _ _ _⟩,
    ⟨inferInstance, domain_definableGraph _ _ _⟩, ⟨inferInstance, domain_definableGraph _ _ _⟩⟩

theorem woodinRecodingHistory_values {θ i : V} (hi : i ∈ θ) :
    (woodinRecodingCarriers (woodinRecodingHistory θ)) ‘ i = kpair.π₁ (woodinRecodingRec i) ∧
    (woodinRecodingOrders (woodinRecodingHistory θ)) ‘ i = kpair.π₁ (kpair.π₂ (woodinRecodingRec i)) ∧
    (woodinRecodingMaps (woodinRecodingHistory θ)) ‘ i = kpair.π₂ (kpair.π₂ (woodinRecodingRec i)) := by
  have hd : domain (woodinRecodingHistory θ) = θ := domain_definableGraph _ _ _
  simp only [woodinRecodingCarriers, woodinRecodingOrders, woodinRecodingMaps,
    value_definableGraph _ _ _ (hd.symm ▸ hi), woodinRecodingHistory_value hi, and_self]

theorem woodinRecodingHistory_agrees {θ η i : V} (hi : i ∈ θ) (hi' : i ∈ η) :
    (woodinRecodingCarriers (woodinRecodingHistory θ)) ‘ i = (woodinRecodingCarriers (woodinRecodingHistory η)) ‘ i ∧
    (woodinRecodingOrders (woodinRecodingHistory θ)) ‘ i = (woodinRecodingOrders (woodinRecodingHistory η)) ‘ i ∧
    (woodinRecodingMaps (woodinRecodingHistory θ)) ‘ i = (woodinRecodingMaps (woodinRecodingHistory η)) ‘ i := by
  exact ⟨(woodinRecodingHistory_values hi).1.trans (woodinRecodingHistory_values hi').1.symm,
    (woodinRecodingHistory_values hi).2.1.trans (woodinRecodingHistory_values hi').2.1.symm,
    (woodinRecodingHistory_values hi).2.2.trans (woodinRecodingHistory_values hi').2.2.symm⟩

theorem woodinNormalizedPrefix_row {Ω θ i : V} [IsOrdinal θ]
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω) (hi : i ∈ θ) :
    (forcingCodeP (woodinNormalizedPrefixCode θ)) ‘ i = (forcingCodeP (woodinNormalizedStageCode i)) ‘ i ∧
    (forcingCodeR (woodinNormalizedPrefixCode θ)) ‘ i = (forcingCodeR (woodinNormalizedStageCode i)) ‘ i := by
  let := IsOrdinal.of_mem hi
  have hsub : succ i ⊆ θ := by
    intro j hj
    rcases mem_succ_iff.mp hj with rfl | hj
    · exact hi
    · exact IsOrdinal.toIsTransitive.mem_trans hj hi
  have he := woodinNormalizedPrefix_extends hΩ hAC hθ hsub
  rw [woodinNormalizedPrefix_successor hΩ hAC (hθ i hi)] at he
  have hs := woodinNormalizedStageCode_valid hΩ hAC (hθ i hi)
  have ht := woodinNormalizedPrefixCode_valid hΩ hAC hθ
  exact ⟨(hs.tableP.value_of_subset ht.tableP he.subP (mem_succ_self i)).symm,
    (hs.tableR.value_of_subset ht.tableR he.subR (mem_succ_self i)).symm⟩

theorem woodinRecodingHistory_family_of_rows {Ω θ : V} [IsOrdinal θ]
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω)
    (h : ∀ i ∈ θ, IsForcingIsomorphism ((forcingCodeP (woodinNormalizedStageCode i)) ‘ i)
      ((forcingCodeR (woodinNormalizedStageCode i)) ‘ i) (kpair.π₁ (woodinRecodingRec i))
      (kpair.π₁ (kpair.π₂ (woodinRecodingRec i))) (kpair.π₂ (kpair.π₂ (woodinRecodingRec i)))) :
    ∀ i ∈ θ, IsForcingIsomorphism ((forcingCodeP (woodinNormalizedPrefixCode θ)) ‘ i)
      ((forcingCodeR (woodinNormalizedPrefixCode θ)) ‘ i)
      ((woodinRecodingCarriers (woodinRecodingHistory θ)) ‘ i)
      ((woodinRecodingOrders (woodinRecodingHistory θ)) ‘ i)
      ((woodinRecodingMaps (woodinRecodingHistory θ)) ‘ i) := by
  intro i hi
  rw [(woodinNormalizedPrefix_row hΩ hAC hθ hi).1, (woodinNormalizedPrefix_row hΩ hAC hθ hi).2,
    (woodinRecodingHistory_values hi).1, (woodinRecodingHistory_values hi).2.1,
    (woodinRecodingHistory_values hi).2.2]
  exact h i hi

end ZFVP
