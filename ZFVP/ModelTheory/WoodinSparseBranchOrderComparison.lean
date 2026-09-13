import ZFVP.ModelTheory.SparseReverseOrderValues
import ZFVP.ModelTheory.WoodinSparseOwnCutoffs

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem woodinSparseInitial_order_comparison {p q : V}
    (hp : p ∈ (woodinSparseInitialCarrier : V)) (hq : q ∈ (woodinSparseInitialCarrier : V)) :
    ⟨p, q⟩ₖ ∈ (woodinSparseInitialOrder : V) ↔
      p ↾ (succ ∅) ∈ forcingFormula ({∅} : V) (({∅} : V) ×ˢ {∅}) isSubsetOf
        (standardTuple ![q ‘ (succ ∅), p ‘ (succ ∅)]) := by
  have he := sparseNormalizedTwoStep_reverse_order_values
    (singletonForcing_preorder (∅ : V)) (singletonForcing_top ∅)
    (saturatedWoodinPrefixPosetName_isName _ _ _ _ _)
    (fun p hp ↦ by
      have he : p = (∅ : V) := by simpa using hp
      subst p
      exact isSparseFunctionOn_empty _) hp hq
  have hp' := (mem_sparsePairCarrier_iff.mp hp).2.1
  have hq' := (mem_sparsePairCarrier_iff.mp hq).2.1
  have hr : ⟨p ↾ (succ ∅), q ↾ (succ ∅)⟩ₖ ∈ (({∅} : V) ×ˢ {∅}) := kpair_mem_iff.mpr ⟨hp', hq'⟩
  simpa only [woodinSparseInitialOrder, saturatedWoodinPrefixOrderName, hr, true_and] using he

theorem woodinSparseStageCode_successor_order_comparison {Ω k p q : V} [IsOrdinal k]
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hk : succ k ⊆ Ω)
    (hp : p ∈ (forcingCodeP (woodinSparseStageCode (succ k))) ‘ (succ k))
    (hq : q ∈ (forcingCodeP (woodinSparseStageCode (succ k))) ‘ (succ k)) :
    ⟨p, q⟩ₖ ∈ (forcingCodeR (woodinSparseStageCode (succ k))) ‘ (succ k) ↔
      ⟨p ↾ (woodinSourceIndex (succ k)), q ↾ (woodinSourceIndex (succ k))⟩ₖ ∈
        (forcingCodeR (woodinSparsePrefixCode (succ k))) ‘ k ∧
      p ↾ (woodinSourceIndex (succ k)) ∈ forcingFormula
        ((forcingCodeP (woodinSparsePrefixCode (succ k))) ‘ k)
        ((forcingCodeR (woodinSparsePrefixCode (succ k))) ‘ k) isSubsetOf
        (standardTuple ![q ‘ (woodinSourceIndex (succ k)), p ‘ (woodinSourceIndex (succ k))]) := by
  rw [(woodinSparseStageCode_successor k).1] at hp hq
  rw [(woodinSparseStageCode_successor k).2]
  have hf := woodinSparsePrefixCode_valid hΩ hAC hk
  exact sparseNormalizedTwoStep_reverse_order_values
    (hf.system.order.preorder k (mem_succ_self k)) (hf.system.tops.top k (mem_succ_self k))
    (saturatedWoodinPrefixPosetName_isName _ _ _ _ _)
    (fun p hp ↦ by
      rw [woodinSourceIndex_successor]
      exact woodinSparsePrefixCode_sparse hΩ hAC hk (mem_succ_self k) hp) hp hq

theorem woodinSparseStageCode_inverse_order_comparison {Ω θ p q : V} [IsOrdinal θ]
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω)
    (h0 : θ ≠ ∅) (hlim : θ ≠ succ (⋃ˢ θ))
    (hn : ¬IsChoicelessInaccessible (woodinLimitCardinal (woodinIterationCardinalPrefix θ)))
    (hp : p ∈ (forcingCodeP (woodinSparseStageCode θ)) ‘ θ)
    (hq : q ∈ (forcingCodeP (woodinSparseStageCode θ)) ‘ θ) :
    ⟨p, q⟩ₖ ∈ (forcingCodeR (woodinSparseStageCode θ)) ‘ θ ↔
      ⟨p ↾ θ, q ↾ θ⟩ₖ ∈ woodinSparseInverseOrder θ (woodinSparsePrefixCode θ) ∧
      p ↾ θ ∈ forcingFormula (woodinSparseInverseBase θ (woodinSparsePrefixCode θ))
        (woodinSparseInverseOrder θ (woodinSparsePrefixCode θ)) isSubsetOf
        (standardTuple ![q ‘ θ, p ‘ θ]) := by
  rw [(woodinSparseStageCode_inverse h0 hlim hn).1] at hp hq
  rw [(woodinSparseStageCode_inverse h0 hlim hn).2]
  have hz : (∅ : V) ∈ θ := (IsOrdinal.subset_iff.mp (empty_subset θ)).resolve_left (fun he ↦ h0 he.symm)
  obtain ⟨hR, ht⟩ := woodinSparsePrefix_inverse_base_laws hΩ hAC hθ hz (ordinal_limit_of_not_successor hlim)
  exact sparseNormalizedTwoStep_reverse_order_values hR ht (forcingSaturatedName_isName _ _ _ _)
    (fun _ hp ↦ ((mem_woodinSparseInverseBase_iff (woodinSparsePrefixCode_valid hΩ hAC hθ)).mp hp).1) hp hq

end ZFVP
