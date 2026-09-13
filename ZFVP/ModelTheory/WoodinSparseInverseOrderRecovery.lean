import ZFVP.ModelTheory.SparseReverseOrderComparison
import ZFVP.ModelTheory.WoodinSparseOwnCutoffs
import ZFVP.ModelTheory.WoodinSparseBaseRecovery

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable {Ω θ p q : V} [IsOrdinal θ]

theorem woodinSparseStageCode_raw_inverse_order_restriction
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω)
    (h0 : θ ≠ ∅) (hlim : θ ≠ succ (⋃ˢ θ))
    (hn : ¬IsChoicelessInaccessible (woodinLimitCardinal (woodinIterationCardinalPrefix θ)))
    (hp : p ∈ woodinSparseInverseBase θ (woodinSparsePrefixCode θ))
    (hq : q ∈ woodinSparseInverseBase θ (woodinSparsePrefixCode θ)) :
    ⟨p, q⟩ₖ ∈ (forcingCodeR (woodinSparseStageCode θ)) ‘ θ ↔
      ⟨p, q⟩ₖ ∈ woodinSparseInverseOrder θ (woodinSparsePrefixCode θ) := by
  have hz : (∅ : V) ∈ θ := (IsOrdinal.subset_iff.mp (empty_subset θ)).resolve_left (fun he ↦ h0 he.symm)
  obtain ⟨hR, ht⟩ := woodinSparsePrefix_inverse_base_laws hΩ hAC hθ hz (ordinal_limit_of_not_successor hlim)
  have ht' := (woodinSparseStageCode_valid hΩ hAC hθ).system.tops.top θ (mem_succ_self θ)
  rw [woodinSparseStageCode_top hΩ hAC hθ] at ht'
  have hm := ht'.1
  rw [(woodinSparseStageCode_inverse h0 hlim hn).1] at hm
  have hw := (mem_sparsePairCarrier_iff.mp hm).2.2
  rw [value_eq_empty_of_not_mem_domain (by rw [domain_empty]; exact not_mem_empty)] at hw
  rw [(woodinSparseStageCode_inverse h0 hlim hn).2]
  exact sparseNormalizedTwoStep_reverse_order_on_base hR ht (forcingSaturatedName_isName _ _ _ _)
    (fun _ hr ↦ ((mem_woodinSparseInverseBase_iff (woodinSparsePrefixCode_valid hΩ hAC hθ)).mp hr).1)
    hw hp hq

theorem woodinSparseStageCode_raw_inverse_order_recovery
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω)
    (h0 : θ ≠ ∅) (hlim : θ ≠ succ (⋃ˢ θ))
    (hn : ¬IsChoicelessInaccessible (woodinLimitCardinal (woodinIterationCardinalPrefix θ))) :
    woodinSparseInverseOrder θ (woodinSparsePrefixCode θ) =
      ((forcingCodeR (woodinSparseStageCode θ)) ‘ θ) ∩
        (sparseCarrierCut ((forcingCodeP (woodinSparseStageCode θ)) ‘ θ) θ ×ˢ
         sparseCarrierCut ((forcingCodeP (woodinSparseStageCode θ)) ‘ θ) θ) := by
  rw [woodinSparseStageCode_raw_inverse_recovery hΩ hAC hθ h0 hlim hn]
  have hz : (∅ : V) ∈ θ := (IsOrdinal.subset_iff.mp (empty_subset θ)).resolve_left (fun he ↦ h0 he.symm)
  have hR := (woodinSparsePrefix_inverse_base_laws hΩ hAC hθ hz (ordinal_limit_of_not_successor hlim)).1
  apply mem_ext
  intro z
  constructor
  · intro hz
    have hzp := hR.1 z hz
    obtain ⟨p, hp, q, hq, rfl⟩ := mem_prod_iff.mp hzp
    exact mem_inter_iff.mpr ⟨(woodinSparseStageCode_raw_inverse_order_restriction hΩ hAC hθ h0 hlim hn hp hq).mpr hz, hzp⟩
  · intro hz
    obtain ⟨hzR, hzP⟩ := mem_inter_iff.mp hz
    obtain ⟨p, hp, q, hq, rfl⟩ := mem_prod_iff.mp hzP
    exact (woodinSparseStageCode_raw_inverse_order_restriction hΩ hAC hθ h0 hlim hn hp hq).mp hzR

theorem woodinSparseStageCode_earlier_raw_inverse_order_restriction {i : V}
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω)
    (hi : i ∈ succ θ) (h0 : i ≠ ∅) (hlim : i ≠ succ (⋃ˢ i))
    (hn : ¬IsChoicelessInaccessible (woodinLimitCardinal (woodinIterationCardinalPrefix i)))
    (hp : p ∈ woodinSparseInverseBase i (woodinSparsePrefixCode i))
    (hq : q ∈ woodinSparseInverseBase i (woodinSparsePrefixCode i)) :
    ⟨p, q⟩ₖ ∈ (forcingCodeR (woodinSparseStageCode θ)) ‘ θ ↔
      ⟨p, q⟩ₖ ∈ woodinSparseInverseOrder i (woodinSparsePrefixCode i) := by
  let := IsOrdinal.of_mem hi
  have hsub := subset_trans (IsOrdinal.subset_iff.mpr (mem_succ_iff.mp hi)) hθ
  have hp' := hp
  have hq' := hq
  rw [← woodinSparseStageCode_raw_inverse_recovery hΩ hAC hsub h0 hlim hn] at hp' hq'
  exact (woodinSparseStageCode_order_restriction hΩ hAC hθ hi
    (mem_sparseCarrierCut_iff.mp hp').1 (mem_sparseCarrierCut_iff.mp hq').1).trans
    (woodinSparseStageCode_raw_inverse_order_restriction hΩ hAC hsub h0 hlim hn hp hq)

theorem woodinSparseStageCode_earlier_raw_inverse_order_recovery {i : V}
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω)
    (hi : i ∈ succ θ) (h0 : i ≠ ∅) (hlim : i ≠ succ (⋃ˢ i))
    (hn : ¬IsChoicelessInaccessible (woodinLimitCardinal (woodinIterationCardinalPrefix i))) :
    woodinSparseInverseOrder i (woodinSparsePrefixCode i) =
      ((forcingCodeR (woodinSparseStageCode θ)) ‘ θ) ∩
        (sparseCarrierCut ((forcingCodeP (woodinSparseStageCode θ)) ‘ θ) i ×ˢ
         sparseCarrierCut ((forcingCodeP (woodinSparseStageCode θ)) ‘ θ) i) := by
  let := IsOrdinal.of_mem hi
  rw [woodinSparseStageCode_earlier_raw_inverse_recovery hΩ hAC hθ hi h0 hlim hn]
  have hsub := subset_trans (IsOrdinal.subset_iff.mpr (mem_succ_iff.mp hi)) hθ
  have hz : (∅ : V) ∈ i := (IsOrdinal.subset_iff.mp (empty_subset i)).resolve_left (fun he ↦ h0 he.symm)
  have hR := (woodinSparsePrefix_inverse_base_laws hΩ hAC hsub hz (ordinal_limit_of_not_successor hlim)).1
  apply mem_ext
  intro z
  constructor
  · intro hz
    have hzp := hR.1 z hz
    obtain ⟨p, hp, q, hq, rfl⟩ := mem_prod_iff.mp hzp
    exact mem_inter_iff.mpr ⟨(woodinSparseStageCode_earlier_raw_inverse_order_restriction
      hΩ hAC hθ hi h0 hlim hn hp hq).mpr hz, hzp⟩
  · intro hz
    obtain ⟨hzR, hzP⟩ := mem_inter_iff.mp hz
    obtain ⟨p, hp, q, hq, rfl⟩ := mem_prod_iff.mp hzP
    exact (woodinSparseStageCode_earlier_raw_inverse_order_restriction hΩ hAC hθ hi h0 hlim hn hp hq).mp hzR

end ZFVP
