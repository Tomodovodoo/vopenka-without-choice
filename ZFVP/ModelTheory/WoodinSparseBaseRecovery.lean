import ZFVP.ModelTheory.WoodinSparseCarrierRecovery

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem sparseCarrierCut_idem {P a b : V} (hab : a ⊆ b) :
    sparseCarrierCut (sparseCarrierCut P b) a = sparseCarrierCut P a := by
  apply mem_ext
  intro p
  simp only [mem_sparseCarrierCut_iff]
  exact ⟨fun h ↦ ⟨h.1.1, h.2⟩, fun h ↦ ⟨⟨h.1, subset_trans h.2 hab⟩, h.2⟩⟩

theorem sparsePairCarrier_base_recovery {a P W : V}
    (hsp : ∀ p ∈ P, IsSparseFunctionOn a p) (h0 : (∅ : V) ∈ W) :
    sparseCarrierCut (sparsePairCarrier a P W) a = P := by
  apply mem_ext
  intro p
  rw [mem_sparseCarrierCut_iff]
  constructor
  · rintro ⟨hp, hd⟩
    have hh := mem_sparsePairCarrier_iff.mp hp
    let := hh.1.1
    simpa only [IsFunction.restrict_eq_self p a hd] using hh.2.1
  · intro hp
    have hh := sparseAppend_mem_pairCarrier hsp hp h0
    rw [sparseAppend_empty] at hh
    exact ⟨hh, (hsp p hp).2.1⟩

variable {Ω θ : V} [IsOrdinal θ]

theorem woodinSparseStageCode_raw_inverse_recovery
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω)
    (h0 : θ ≠ ∅) (hlim : θ ≠ succ (⋃ˢ θ))
    (hn : ¬IsChoicelessInaccessible (woodinLimitCardinal (woodinIterationCardinalPrefix θ))) :
    sparseCarrierCut ((forcingCodeP (woodinSparseStageCode θ)) ‘ θ) θ =
      woodinSparseInverseBase θ (woodinSparsePrefixCode θ) := by
  have ht := (woodinSparseStageCode_valid hΩ hAC hθ).system.tops.top θ (mem_succ_self θ)
  rw [woodinSparseStageCode_top hΩ hAC hθ] at ht
  have hmem := ht.1
  rw [(woodinSparseStageCode_inverse h0 hlim hn).1] at hmem ⊢
  change (∅ : V) ∈ sparsePairCarrier θ (woodinSparseInverseBase θ (woodinSparsePrefixCode θ))
    (woodinSparseInversePool θ (woodinSparsePrefixCode θ)) at hmem
  have hw := (mem_sparsePairCarrier_iff.mp hmem).2.2
  rw [value_eq_empty_of_not_mem_domain (by rw [domain_empty]; exact not_mem_empty)] at hw
  exact sparsePairCarrier_base_recovery
    (fun _ hp ↦ ((mem_woodinSparseInverseBase_iff (woodinSparsePrefixCode_valid hΩ hAC hθ)).mp hp).1) hw

theorem woodinSparseStageCode_earlier_raw_inverse_recovery
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω)
    {i : V} (hi : i ∈ succ θ) (h0 : i ≠ ∅) (hlim : i ≠ succ (⋃ˢ i))
    (hn : ¬IsChoicelessInaccessible (woodinLimitCardinal (woodinIterationCardinalPrefix i))) :
    sparseCarrierCut ((forcingCodeP (woodinSparseStageCode θ)) ‘ θ) i =
      woodinSparseInverseBase i (woodinSparsePrefixCode i) := by
  let := IsOrdinal.of_mem hi
  have hisub : i ⊆ Ω := subset_trans (IsOrdinal.subset_iff.mpr (mem_succ_iff.mp hi)) hθ
  have hz : (∅ : V) ∈ i := (IsOrdinal.subset_iff.mp (empty_subset i)).resolve_left (fun he ↦ h0 he.symm)
  have he := woodinSparseStageCode_carrier_recovery hΩ hAC hθ hi
  rw [woodinSourceIndex_limit i hz (ordinal_limit_of_not_successor hlim)] at he
  rw [← sparseCarrierCut_idem (P := (forcingCodeP (woodinSparseStageCode θ)) ‘ θ)
    (a := i) (b := succ i) (fun _ hx ↦ mem_succ_iff.mpr (Or.inr hx)), ← he]
  exact woodinSparseStageCode_raw_inverse_recovery hΩ hAC hisub h0 hlim hn

end ZFVP


