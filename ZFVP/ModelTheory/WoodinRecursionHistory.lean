import ZFVP.ModelTheory.WoodinIterationRecursion

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem woodinIterationHistory_codes_table (θ : V) :
    IsIterationTable θ (woodinHistoryCodes (woodinIterationHistory θ)) := by
  unfold woodinHistoryCodes woodinIterationHistory
  exact ⟨inferInstance, (domain_definableGraph _ _ _).trans (domain_definableGraph _ _ _)⟩

theorem woodinIterationHistory_cardinals_table (θ : V) :
    IsIterationTable θ (woodinHistoryCardinals (woodinIterationHistory θ)) := by
  unfold woodinHistoryCardinals woodinIterationHistory
  exact ⟨inferInstance, (domain_definableGraph _ _ _).trans (domain_definableGraph _ _ _)⟩

theorem woodinIterationHistory_code_value {θ i : V} (hi : i ∈ θ) :
    (woodinHistoryCodes (woodinIterationHistory θ)) ‘ i = kpair.π₁ (woodinIterationRec i) := by
  unfold woodinHistoryCodes woodinIterationHistory
  rw [value_definableGraph _ _ _ (by simpa only [domain_definableGraph] using hi),
    value_definableGraph _ _ _ hi]

theorem woodinIterationHistory_cardinal_value {θ i : V} (hi : i ∈ θ) :
    (woodinHistoryCardinals (woodinIterationHistory θ)) ‘ i = kpair.π₂ (woodinIterationRec i) := by
  unfold woodinHistoryCardinals woodinIterationHistory
  rw [value_definableGraph _ _ _ (by simpa only [domain_definableGraph] using hi),
    value_definableGraph _ _ _ hi]

theorem woodinIterationRec_extends_previous {δ θ i : V} [IsOrdinal θ]
    (h : IsWoodinIterationHistory δ θ (woodinHistoryCodes (woodinIterationHistory θ))
      (woodinHistoryCardinals (woodinIterationHistory θ))) (hi : i ∈ θ) :
    ForcingCodeExtends (kpair.π₁ (woodinIterationRec i)) (kpair.π₁ (woodinIterationRec θ)) ∧
      kpair.π₂ (woodinIterationRec i) ⊆ kpair.π₂ (woodinIterationRec θ) := by
  have hn : θ ≠ ∅ := by rintro rfl; exact not_mem_empty hi
  have hc := forcingIterationCodeUnion_extends
    (H := woodinHistoryCodes (woodinIterationHistory θ)) hi
  rw [woodinIterationHistory_code_value hi] at hc
  have hK := woodinHistoryCardinalUnion_extends
    (J := woodinHistoryCardinals (woodinIterationHistory θ)) hi
  rw [woodinIterationHistory_cardinal_value hi] at hK
  rw [woodinIterationRec_rule θ]
  exact ⟨hc.trans (woodinStageRule_code_extends h.codes.union_code hn),
    subset_trans hK (woodinStageRule_cardinals_extend h.cardinal_union_table hn)⟩

/-- The induction hypotheses at earlier indices assemble the actual recursive history. -/
theorem woodinIterationHistory_of_previous {δ θ : V} [IsOrdinal θ]
    (hs : ∀ i ∈ θ, IsWoodinIteration δ (succ i) (kpair.π₁ (woodinIterationRec i))
      (kpair.π₂ (woodinIterationRec i)))
    (hh : ∀ i ∈ θ, IsWoodinIterationHistory δ i
      (woodinHistoryCodes (woodinIterationHistory i))
      (woodinHistoryCardinals (woodinIterationHistory i))) :
    IsWoodinIterationHistory δ θ (woodinHistoryCodes (woodinIterationHistory θ))
      (woodinHistoryCardinals (woodinIterationHistory θ)) := by
  have he (i : V) (hi : i ∈ θ) (j : V) (hj : j ∈ θ) (hij : i ⊆ j) :
      ForcingCodeExtends (kpair.π₁ (woodinIterationRec i)) (kpair.π₁ (woodinIterationRec j)) ∧
        kpair.π₂ (woodinIterationRec i) ⊆ kpair.π₂ (woodinIterationRec j) := by
    let := IsOrdinal.of_mem hi
    let := IsOrdinal.of_mem hj
    rcases IsOrdinal.subset_iff.mp hij with rfl | hij
    · exact ⟨ForcingCodeExtends.refl _, subset_refl _⟩
    · exact woodinIterationRec_extends_previous (hh j hj) hij
  refine ⟨⟨woodinIterationHistory_codes_table θ, ?_, ?_⟩,
    woodinIterationHistory_cardinals_table θ, ?_, ?_⟩
  · intro i hi
    rw [woodinIterationHistory_code_value hi]
    exact (hs i hi).code
  · intro i hi j hj hij
    rw [woodinIterationHistory_code_value hi, woodinIterationHistory_code_value hj]
    exact (he i hi j hj hij).1
  · intro i hi
    rw [woodinIterationHistory_code_value hi, woodinIterationHistory_cardinal_value hi]
    exact hs i hi
  · intro i hi j hj hij
    rw [woodinIterationHistory_cardinal_value hi, woodinIterationHistory_cardinal_value hj]
    exact (he i hi j hj hij).2

theorem woodinIterationPrefix_of_previous {δ θ : V} [IsOrdinal θ]
    (hs : ∀ i ∈ θ, IsWoodinIteration δ (succ i) (kpair.π₁ (woodinIterationRec i))
      (kpair.π₂ (woodinIterationRec i)))
    (hh : ∀ i ∈ θ, IsWoodinIterationHistory δ i
      (woodinHistoryCodes (woodinIterationHistory i))
      (woodinHistoryCardinals (woodinIterationHistory i))) :
    IsWoodinIteration δ θ (woodinIterationPrefix θ) (woodinIterationCardinalPrefix θ) :=
  (woodinIterationHistory_of_previous hs hh).union_iteration

end ZFVP
