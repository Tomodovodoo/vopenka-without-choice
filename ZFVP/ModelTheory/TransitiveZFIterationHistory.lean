import ZFVP.ModelTheory.TransitiveZFIterationTables
import ZFVP.ModelTheory.WoodinIterationRecursion

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
namespace TransitiveZF
variable (U : V) [IsTransitive U] [Nonempty (SetDomain U)] [(SetDomain U)↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem iterationTableUnion_val (I : SetDomain U) (F : SetDomain U → SetDomain U)
    (hF : ℒₛₑₜ-function₁ F) (G : V → V) (hG : ℒₛₑₜ-function₁ G)
    (hval : ∀ x ∈ I, (F x).val = G x.val) :
    (iterationTableUnion I F hF).val = iterationTableUnion I.val G hG := by
  unfold iterationTableUnion
  rw [sUnion_val U, repl_val U I F hF G hG hval]

theorem forcingHistoryTable_val (θ H : SetDomain U) (c : SetDomain U → SetDomain U)
    (hc : ℒₛₑₜ-function₁ c) (d : V → V) (hd : ℒₛₑₜ-function₁ d)
    (hval : ∀ x, (c x).val = d x.val) :
    (forcingHistoryTable θ H c hc).val = forcingHistoryTable θ.val H.val d hd := by
  unfold forcingHistoryTable
  apply iterationTableUnion_val U
  intro i _
  rw [hval, value_val_total U]

theorem forcingIterationCodeUnion_val (θ H : SetDomain U) :
    (forcingIterationCodeUnion θ H).val = forcingIterationCodeUnion θ.val H.val := by
  unfold forcingIterationCodeUnion
  rw [forcingIterationCode_val U]
  congr 1
  · exact forcingHistoryTable_val U θ H _ _ _ _ (forcingCodeP_val U)
  · exact forcingHistoryTable_val U θ H _ _ _ _ (forcingCodeR_val U)
  · exact forcingHistoryTable_val U θ H _ _ _ _ (forcingCodeπ_val U)
  · exact forcingHistoryTable_val U θ H _ _ _ _ (forcingCodeE_val U)
  · exact forcingHistoryTable_val U θ H _ _ _ _ (forcingCodeL_val U)
  · exact forcingHistoryTable_val U θ H _ _ _ _ (forcingCodet_val U)

theorem woodinHistoryCardinalUnion_val (θ H : SetDomain U) :
    (woodinHistoryCardinalUnion θ H).val = woodinHistoryCardinalUnion θ.val H.val := by
  unfold woodinHistoryCardinalUnion
  apply iterationTableUnion_val U
  intro i _
  exact value_val_total U H i

theorem woodinHistoryCodes_val (H : SetDomain U) :
    (woodinHistoryCodes H).val = woodinHistoryCodes H.val := by
  unfold woodinHistoryCodes
  rw [← domain_val U]
  apply definableGraph_val U
  intro i _
  rw [kpair_first_val U, value_val_total U]

theorem woodinHistoryCardinals_val (H : SetDomain U) :
    (woodinHistoryCardinals H).val = woodinHistoryCardinals H.val := by
  unfold woodinHistoryCardinals
  rw [← domain_val U]
  apply definableGraph_val U
  intro i _
  rw [kpair_second_val U, value_val_total U]

theorem woodinLimitCardinal_val (K : SetDomain U) :
    (woodinLimitCardinal K).val = woodinLimitCardinal K.val := by
  simp only [woodinLimitCardinal, sUnion_val U, range_val U]

end TransitiveZF
end ZFVP
