import ZFVP.ModelTheory.WoodinRecodedEndpoint

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem woodinRecodingHistory_next (θ : V) :
    woodinRecodingCarriers (woodinRecodingHistory (succ θ)) =
      forcingFamilyNext θ (woodinRecodingCarriers (woodinRecodingHistory θ)) (kpair.π₁ (woodinRecodingRec θ)) ∧
    woodinRecodingOrders (woodinRecodingHistory (succ θ)) =
      forcingFamilyNext θ (woodinRecodingOrders (woodinRecodingHistory θ)) (kpair.π₁ (kpair.π₂ (woodinRecodingRec θ))) ∧
    woodinRecodingMaps (woodinRecodingHistory (succ θ)) =
      forcingFamilyNext θ (woodinRecodingMaps (woodinRecodingHistory θ)) (kpair.π₂ (kpair.π₂ (woodinRecodingRec θ))) := by
  have heq (X Y a : V) (hX : IsIterationTable (succ θ) X)
      (hnew : X ‘ θ = a) (hold : ∀ i ∈ θ, X ‘ i = Y ‘ i) : X = forcingFamilyNext θ Y a := by
    let := hX.function
    let := (forcingFamilyNext_table θ Y a).function
    apply functions_eq_of_domain_values
    · rw [hX.domain_eq, (forcingFamilyNext_table θ Y a).domain_eq]
    intro i hi
    rw [hX.domain_eq] at hi
    rcases mem_succ_iff.mp hi with rfl | hi
    · rw [forcingFamilyNext_new, hnew]
    · rw [forcingFamilyNext_old hi, hold i hi]
  exact ⟨heq _ _ _ (woodinRecodingHistory_tables (succ θ)).1 (woodinRecodingHistory_values (mem_succ_self θ)).1
      (fun i hi ↦ (woodinRecodingHistory_agrees (mem_succ_iff.mpr (Or.inr hi)) hi).1),
    heq _ _ _ (woodinRecodingHistory_tables (succ θ)).2.1 (woodinRecodingHistory_values (mem_succ_self θ)).2.1
      (fun i hi ↦ (woodinRecodingHistory_agrees (mem_succ_iff.mpr (Or.inr hi)) hi).2.1),
    heq _ _ _ (woodinRecodingHistory_tables (succ θ)).2.2 (woodinRecodingHistory_values (mem_succ_self θ)).2.2
      (fun i hi ↦ (woodinRecodingHistory_agrees (mem_succ_iff.mpr (Or.inr hi)) hi).2.2)⟩

theorem woodinRecodedStageCode_successor (k : V) [IsOrdinal k] :
    woodinRecodedStageCode (succ k) = woodinRecodedSuccessorNextCode k
      (woodinRecodingCarriers (woodinRecodingHistory (succ k)))
      (woodinRecodingOrders (woodinRecodingHistory (succ k)))
      (woodinRecodingMaps (woodinRecodingHistory (succ k))) := by
  have hz : succ k ≠ (∅ : V) := by
    intro he
    exact not_mem_empty (he ▸ mem_succ_self k)
  rw [woodinRecodedStageCode, (woodinRecodingHistory_next (succ k)).1,
    (woodinRecodingHistory_next (succ k)).2.1, (woodinRecodingHistory_next (succ k)).2.2,
    woodinRecodingRec_rule]
  simp only [woodinRecodingRule, woodinRecodingRowRule, ite_eq_right hz, sUnion_succ_of_transitive,
    ite_true, woodinRecodingSuccessorRow, kpair.π₁_kpair, kpair.π₂_kpair, woodinRecodedSuccessorNextCode]

theorem woodinRecodedStageCode_direct {θ : V} [IsOrdinal θ]
    (h0 : θ ≠ ∅) (hlim : θ ≠ succ (⋃ˢ θ))
    (hi : IsChoicelessInaccessible (woodinLimitCardinal (woodinIterationCardinalPrefix θ))) :
    woodinRecodedStageCode θ = woodinRecodedDirectNextCode θ
      (woodinRecodingCarriers (woodinRecodingHistory θ))
      (woodinRecodingOrders (woodinRecodingHistory θ))
      (woodinRecodingMaps (woodinRecodingHistory θ)) := by
  rw [woodinRecodedStageCode, (woodinRecodingHistory_next θ).1,
    (woodinRecodingHistory_next θ).2.1, (woodinRecodingHistory_next θ).2.2, woodinRecodingRec_rule]
  simp only [woodinRecodingRule, woodinRecodingRowRule, ite_eq_right h0, ite_eq_right hlim, ite_eq_left hi,
    woodinRecodingDirectRow, kpair.π₁_kpair, kpair.π₂_kpair, woodinRecodedDirectNextCode]

theorem woodinRecodedStageCode_inverse {θ : V} [IsOrdinal θ]
    (h0 : θ ≠ ∅) (hlim : θ ≠ succ (⋃ˢ θ))
    (hi : ¬IsChoicelessInaccessible (woodinLimitCardinal (woodinIterationCardinalPrefix θ))) :
    woodinRecodedStageCode θ = woodinRecodedInverseNextCode θ
      (woodinRecodingCarriers (woodinRecodingHistory θ))
      (woodinRecodingOrders (woodinRecodingHistory θ))
      (woodinRecodingMaps (woodinRecodingHistory θ)) := by
  rw [woodinRecodedStageCode, (woodinRecodingHistory_next θ).1,
    (woodinRecodingHistory_next θ).2.1, (woodinRecodingHistory_next θ).2.2, woodinRecodingRec_rule]
  simp only [woodinRecodingRule, woodinRecodingRowRule, ite_eq_right h0, ite_eq_right hlim, ite_eq_right hi,
    woodinRecodingInverseRow, kpair.π₁_kpair, kpair.π₂_kpair, woodinRecodedInverseNextCode]

theorem woodinRecodedStageCode_eq_prefix {Ω θ : V} [IsOrdinal θ]
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ∈ Ω) :
    woodinRecodedStageCode θ = woodinRecodedPrefixCode (succ θ) := by
  unfold woodinRecodedStageCode woodinRecodedPrefixCode
  rw [woodinNormalizedPrefix_successor hΩ hAC hθ]

theorem woodinRecodedStageCode_valid {Ω θ : V} [IsOrdinal θ]
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω) :
    IsForcingIterationCode (succ θ) (woodinRecodedStageCode θ) := by
  let := hΩ.inaccessible.1
  rcases IsOrdinal.subset_iff.mp hθ with rfl | hθ
  · exact woodinRecodedStageCode_endpoint_valid hΩ hAC
  · rw [woodinRecodedStageCode_eq_prefix hΩ hAC hθ]
    apply woodinRecodedPrefixCode_valid hΩ hAC
    intro i hi
    rcases mem_succ_iff.mp hi with rfl | hi
    · exact hθ
    · exact IsOrdinal.toIsTransitive.mem_trans hi hθ

end ZFVP
