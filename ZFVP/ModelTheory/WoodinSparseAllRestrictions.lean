import ZFVP.ModelTheory.WoodinSparseBaseRecovery

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable {Ω θ p : V} [IsOrdinal θ]

theorem woodinSparseStageCode_restrict_completed
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω)
    {i : V} (hi : i ∈ succ θ)
    (hp : p ∈ (forcingCodeP (woodinSparseStageCode θ)) ‘ θ) :
    p ↾ (succ (woodinSourceIndex i)) ∈ (forcingCodeP (woodinSparseStageCode i)) ‘ i := by
  rcases mem_succ_iff.mp hi with he | hi
  · subst i
    have hs := woodinSparseStageCode_sparse hΩ hAC hθ hp
    let := hs.1
    rwa [IsFunction.restrict_eq_self p _ hs.2.1]
  · exact woodinSparseStageCode_restrict_mem hΩ hAC hθ hi hp

theorem woodinSparseStageCode_restrict_own_limit
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω)
    (h0 : θ ≠ ∅) (hlim : θ ≠ succ (⋃ˢ θ))
    (hp : p ∈ (forcingCodeP (woodinSparseStageCode θ)) ‘ θ) :
    p ↾ θ ∈ (forcingCodeP (woodinSparseStageCode θ)) ‘ θ := by
  have hs := woodinSparseStageCode_sparse hΩ hAC hθ hp
  let := hs.1
  by_cases hn : IsChoicelessInaccessible (woodinLimitCardinal (woodinIterationCardinalPrefix θ))
  · rwa [IsFunction.restrict_eq_self p θ (woodinSparseStageCode_direct_domain hΩ hAC hθ h0 hlim hn hp)]
  · have hp' := hp
    rw [(woodinSparseStageCode_inverse h0 hlim hn).1] at hp'
    have hr := (mem_sparsePairCarrier_iff.mp hp').2.1
    rw [← woodinSparseStageCode_raw_inverse_recovery hΩ hAC hθ h0 hlim hn] at hr
    exact (mem_sparseCarrierCut_iff.mp hr).1

theorem woodinSparseStageCode_restrict_limit
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω)
    {a : V} [IsOrdinal a] (h0 : a ≠ ∅) (hlim : a ≠ succ (⋃ˢ a))
    (hp : p ∈ (forcingCodeP (woodinSparseStageCode θ)) ‘ θ) :
    p ↾ a ∈ (forcingCodeP (woodinSparseStageCode θ)) ‘ θ := by
  have hs := woodinSparseStageCode_sparse hΩ hAC hθ hp
  let := hs.1
  have hl := ordinal_limit_of_not_successor hlim
  rcases IsOrdinal.mem_trichotomy a θ with ha | he | ha
  · have hz : (∅ : V) ∈ a := (IsOrdinal.subset_iff.mp (empty_subset a)).resolve_left (fun he ↦ h0 he.symm)
    have hr := woodinSparseStageCode_restrict_mem hΩ hAC hθ ha hp
    have hsub := subset_trans (IsOrdinal.toIsTransitive.transitive _ ha) hθ
    have hh := woodinSparseStageCode_restrict_own_limit hΩ hAC hsub h0 hlim hr
    rw [woodinSourceIndex_limit a hz hl,
      restrict_restrict_of_subset (mem_subset_refl a)] at hh
    exact woodinSparseStageCode_carrier_subset hΩ hAC hθ (mem_succ_iff.mpr (Or.inr ha)) _ hh
  · subst a
    exact woodinSparseStageCode_restrict_own_limit hΩ hAC hθ h0 hlim hp
  · have hb := woodinSourceIndex_mem_of_mem hl ha
    have hd : domain p ⊆ a := subset_trans hs.2.1 (by
      intro x hx
      rcases mem_succ_iff.mp hx with he | hx
      · exact he ▸ hb
      · exact IsOrdinal.toIsTransitive.mem_trans hx hb)
    rwa [IsFunction.restrict_eq_self p a hd]

theorem woodinSparseStageCode_restrict_successor
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω)
    {a : V} [IsOrdinal a]
    (hp : p ∈ (forcingCodeP (woodinSparseStageCode θ)) ‘ θ) :
    p ↾ (succ a) ∈ (forcingCodeP (woodinSparseStageCode θ)) ‘ θ := by
  have hs := woodinSparseStageCode_sparse hΩ hAC hθ hp
  let := hs.1
  rcases IsOrdinal.mem_trichotomy a (woodinSourceIndex θ) with ha | he | ha
  · rcases woodinSourceIndex_cases ha with he | ⟨i, hi, he⟩
    · subst a
      have hd : domain (p ↾ (succ (∅ : V))) ⊆ (∅ : V) := by
        intro x hx
        rw [domain_restrict_eq] at hx
        rcases mem_succ_iff.mp (mem_inter_iff.mp hx).2 with he | hx'
        · subst x
          exact False.elim (woodinSparseStageCode_no_zero hΩ hAC hθ hp (mem_inter_iff.mp hx).1)
        · exact hx'
      have he : p ↾ (succ (∅ : V)) = ∅ := by
        simpa only [restrict_empty_domain] using (IsFunction.restrict_eq_self (p ↾ (succ (∅ : V))) ∅ hd).symm
      rw [he]
      have ht := (woodinSparseStageCode_valid hΩ hAC hθ).system.tops.top θ (mem_succ_self θ)
      rw [woodinSparseStageCode_top hΩ hAC hθ] at ht
      exact ht.1
    · subst a
      exact woodinSparseStageCode_carrier_subset hΩ hAC hθ (mem_succ_iff.mpr (Or.inr hi)) _
        (woodinSparseStageCode_restrict_mem hΩ hAC hθ hi hp)
  · subst a
    rwa [IsFunction.restrict_eq_self p _ hs.2.1]
  · have hd : domain p ⊆ succ a := subset_trans hs.2.1 (by
      intro x hx
      apply mem_succ_iff.mpr
      right
      rcases mem_succ_iff.mp hx with he | hx
      · exact he ▸ ha
      · exact IsOrdinal.toIsTransitive.mem_trans hx ha)
    rwa [IsFunction.restrict_eq_self p _ hd]

theorem woodinSparseStageCode_restrict_any
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω)
    {a : V} [IsOrdinal a]
    (hp : p ∈ (forcingCodeP (woodinSparseStageCode θ)) ‘ θ) :
    p ↾ a ∈ (forcingCodeP (woodinSparseStageCode θ)) ‘ θ := by
  by_cases hz : a = ∅
  · subst a
    rw [restrict_empty_domain]
    have ht := (woodinSparseStageCode_valid hΩ hAC hθ).system.tops.top θ (mem_succ_self θ)
    rw [woodinSparseStageCode_top hΩ hAC hθ] at ht
    exact ht.1
  · by_cases he : a = succ (⋃ˢ a)
    · have hm : ⋃ˢ a ∈ a := (congrArg (fun x : V ↦ ⋃ˢ a ∈ x) he).mpr (mem_succ_self _)
      let := IsOrdinal.of_mem hm
      rw [he]
      exact woodinSparseStageCode_restrict_successor hΩ hAC hθ hp
    · exact woodinSparseStageCode_restrict_limit hΩ hAC hθ hz he hp

end ZFVP
