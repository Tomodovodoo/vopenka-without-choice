import ZFVP.ModelTheory.WoodinSparseStageLaws

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem woodinSparseRecodingRec_initial :
    (woodinSparseRecodingRec (∅ : V)) = woodinSparseRecodingInitialRow := by
  rw [woodinSparseRecodingRec_rule]
  simp only [woodinSparseRecodingRule, woodinSparseRecodingRowRule, ite_true]

theorem woodinSparseRecodingRec_successor (k : V) [IsOrdinal k] :
    woodinSparseRecodingRec (succ k) = woodinSparseRecodingSuccessorRow k
      (woodinSparsePrefixCode (succ k)) (woodinRecodingMaps (woodinSparseRecodingHistory (succ k))) := by
  have hz : succ k ≠ (∅ : V) := by
    intro he
    exact not_mem_empty (he ▸ mem_succ_self k)
  rw [woodinSparseRecodingRec_rule]
  simp only [woodinSparseRecodingRule, woodinSparseRecodingRowRule, ite_eq_right hz,
    sUnion_succ_of_transitive, ite_true, woodinSparsePrefixCode]

theorem woodinSparseRecodingRec_direct {θ : V} [IsOrdinal θ]
    (h0 : θ ≠ ∅) (hlim : θ ≠ succ (⋃ˢ θ))
    (hn : IsChoicelessInaccessible (woodinLimitCardinal (woodinIterationCardinalPrefix θ))) :
    woodinSparseRecodingRec θ = woodinSparseRecodingDirectRow θ
      (woodinSparsePrefixCode θ) (woodinRecodingMaps (woodinSparseRecodingHistory θ)) := by
  rw [woodinSparseRecodingRec_rule]
  simp only [woodinSparseRecodingRule, woodinSparseRecodingRowRule, ite_eq_right h0,
    ite_eq_right hlim, ite_eq_left hn, woodinSparsePrefixCode]

theorem woodinSparseRecodingRec_inverse {θ : V} [IsOrdinal θ]
    (h0 : θ ≠ ∅) (hlim : θ ≠ succ (⋃ˢ θ))
    (hn : ¬IsChoicelessInaccessible (woodinLimitCardinal (woodinIterationCardinalPrefix θ))) :
    woodinSparseRecodingRec θ = woodinSparseRecodingInverseRow θ
      (woodinSparsePrefixCode θ) (woodinRecodingMaps (woodinSparseRecodingHistory θ)) := by
  rw [woodinSparseRecodingRec_rule]
  simp only [woodinSparseRecodingRule, woodinSparseRecodingRowRule, ite_eq_right h0,
    ite_eq_right hlim, ite_eq_right hn, woodinSparsePrefixCode]

theorem woodinSparseStageCode_row (θ : V) :
    (forcingCodeP (woodinSparseStageCode θ)) ‘ θ = kpair.π₁ (woodinSparseRecodingRec θ) ∧
    (forcingCodeR (woodinSparseStageCode θ)) ‘ θ = kpair.π₁ (kpair.π₂ (woodinSparseRecodingRec θ)) := by
  simp only [woodinSparseStageCode, forcingRecodedCode, forcingCodeP_code, forcingCodeR_code,
    (woodinSparseRecodingHistory_values (mem_succ_self θ)).1,
    (woodinSparseRecodingHistory_values (mem_succ_self θ)).2.1, and_self]

theorem woodinSparseStageCode_initial :
    (forcingCodeP (woodinSparseStageCode (∅ : V))) ‘ ∅ = woodinSparseInitialCarrier ∧
    (forcingCodeR (woodinSparseStageCode (∅ : V))) ‘ ∅ = woodinSparseInitialOrder := by
  rw [(woodinSparseStageCode_row ∅).1, (woodinSparseStageCode_row ∅).2, woodinSparseRecodingRec_initial]
  simp only [woodinSparseRecodingInitialRow, kpair.π₁_kpair, kpair.π₂_kpair, and_self]

theorem woodinSparseStageCode_successor (k : V) [IsOrdinal k] :
    (forcingCodeP (woodinSparseStageCode (succ k))) ‘ (succ k) =
      woodinSparseSuccessorCarrier k (woodinSparsePrefixCode (succ k)) ∧
    (forcingCodeR (woodinSparseStageCode (succ k))) ‘ (succ k) =
      woodinSparseSuccessorOrder k (woodinSparsePrefixCode (succ k)) := by
  rw [(woodinSparseStageCode_row (succ k)).1, (woodinSparseStageCode_row (succ k)).2, woodinSparseRecodingRec_successor]
  simp only [woodinSparseRecodingSuccessorRow, kpair.π₁_kpair, kpair.π₂_kpair, and_self]

theorem woodinSparseStageCode_direct {θ : V} [IsOrdinal θ]
    (h0 : θ ≠ ∅) (hlim : θ ≠ succ (⋃ˢ θ))
    (hn : IsChoicelessInaccessible (woodinLimitCardinal (woodinIterationCardinalPrefix θ))) :
    (forcingCodeP (woodinSparseStageCode θ)) ‘ θ = woodinSparseDirectBase θ (woodinSparsePrefixCode θ) ∧
    (forcingCodeR (woodinSparseStageCode θ)) ‘ θ = woodinSparseDirectOrder θ (woodinSparsePrefixCode θ) := by
  rw [(woodinSparseStageCode_row θ).1, (woodinSparseStageCode_row θ).2, woodinSparseRecodingRec_direct h0 hlim hn]
  simp only [woodinSparseRecodingDirectRow, kpair.π₁_kpair, kpair.π₂_kpair, and_self]

theorem woodinSparseStageCode_inverse {θ : V} [IsOrdinal θ]
    (h0 : θ ≠ ∅) (hlim : θ ≠ succ (⋃ˢ θ))
    (hn : ¬IsChoicelessInaccessible (woodinLimitCardinal (woodinIterationCardinalPrefix θ))) :
    (forcingCodeP (woodinSparseStageCode θ)) ‘ θ = woodinSparseCompletedInverseCarrier θ (woodinSparsePrefixCode θ) ∧
    (forcingCodeR (woodinSparseStageCode θ)) ‘ θ = woodinSparseCompletedInverseOrder θ (woodinSparsePrefixCode θ) := by
  rw [(woodinSparseStageCode_row θ).1, (woodinSparseStageCode_row θ).2, woodinSparseRecodingRec_inverse h0 hlim hn]
  simp only [woodinSparseRecodingInverseRow, kpair.π₁_kpair, kpair.π₂_kpair, and_self]

end ZFVP
