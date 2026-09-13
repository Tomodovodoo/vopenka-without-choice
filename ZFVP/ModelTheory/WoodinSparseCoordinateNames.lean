import ZFVP.ModelTheory.WoodinSparsePoolRecovery
import ZFVP.ModelTheory.WoodinSparseAllRestrictions
import ZFVP.SetTheory.ForcingRetraction

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem sparsePairCarrier_coordinate_isName {a P W p : V}
    (hsp : ∀ p ∈ P, IsSparseFunctionOn a p) (h0 : (∅ : V) ∈ sparsePairCarrier a P W)
    (hW : ∀ τ ∈ W, IsForcingName P τ) (hp : p ∈ sparsePairCarrier a P W) :
    IsForcingName (sparseCarrierCut (sparsePairCarrier a P W) a) (p ‘ a) := by
  have hw := (mem_sparsePairCarrier_iff.mp h0).2.2
  rw [value_eq_empty_of_not_mem_domain (by rw [domain_empty]; exact not_mem_empty)] at hw
  rw [sparsePairCarrier_base_recovery hsp hw]
  exact hW _ (mem_sparsePairCarrier_iff.mp hp).2.2

variable {Ω θ : V} [IsOrdinal θ]
theorem woodinSparseStageCode_own_coordinate_isName
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω)
    {p : V} (hp : p ∈ (forcingCodeP (woodinSparseStageCode θ)) ‘ θ) :
    IsForcingName (sparseCarrierCut ((forcingCodeP (woodinSparseStageCode θ)) ‘ θ)
      (woodinSourceIndex θ)) (p ‘ (woodinSourceIndex θ)) := by
  have ht := (woodinSparseStageCode_valid hΩ hAC hθ).system.tops.top θ (mem_succ_self θ)
  rw [woodinSparseStageCode_top hΩ hAC hθ] at ht
  have h0 := ht.1
  by_cases hz : θ = ∅
  · subst θ
    rw [(woodinSparseStageCode_initial).1] at hp h0 ⊢
    rw [woodinSourceIndex_zero]
    apply sparsePairCarrier_coordinate_isName _ h0 _ hp
    · intro p hp
      have he : p = (∅ : V) := by simpa using hp
      subst p
      exact isSparseFunctionOn_empty _
    · intro τ hτ
      exact (mem_sep_iff.mp hτ).2.1
  · by_cases he : θ = succ (⋃ˢ θ)
    · have hm : ⋃ˢ θ ∈ θ := (congrArg (fun x : V ↦ ⋃ˢ θ ∈ x) he).mpr (mem_succ_self _)
      let := IsOrdinal.of_mem hm
      generalize hk : ⋃ˢ θ = k at he
      have : IsOrdinal k := hk ▸ (inferInstance : IsOrdinal (⋃ˢ θ))
      subst θ
      rw [(woodinSparseStageCode_successor k).1] at hp h0 ⊢
      apply sparsePairCarrier_coordinate_isName _ h0 _ hp
      · intro p hp
        rw [woodinSourceIndex_successor]
        exact woodinSparsePrefixCode_sparse hΩ hAC hθ (mem_succ_self k) hp
      · intro τ hτ
        simp only [woodinSparseSuccessorPool, normalizedNamePool, mem_sep_iff] at hτ
        exact hτ.2.1
    · have hz' : (∅ : V) ∈ θ := (IsOrdinal.subset_iff.mp (empty_subset θ)).resolve_left (fun h ↦ hz h.symm)
      rw [woodinSourceIndex_limit θ hz' (ordinal_limit_of_not_successor he)]
      by_cases hn : IsChoicelessInaccessible (woodinLimitCardinal (woodinIterationCardinalPrefix θ))
      · rw [value_eq_empty_of_not_mem_domain (woodinSparseStageCode_direct_no_self hΩ hAC hθ hz he hn hp)]
        exact empty_forcingName _
      · rw [(woodinSparseStageCode_inverse hz he hn).1] at hp h0 ⊢
        apply sparsePairCarrier_coordinate_isName _ h0 _ hp
        · intro p hp
          exact ((mem_woodinSparseInverseBase_iff (woodinSparsePrefixCode_valid hΩ hAC hθ)).mp hp).1
        · intro τ hτ
          simp only [woodinSparseInversePool, normalizedNamePool, mem_sep_iff] at hτ
          exact hτ.2.1

theorem woodinSparseStageCode_coordinate_isName
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω)
    {a p : V} [IsOrdinal a]
    (hp : p ∈ (forcingCodeP (woodinSparseStageCode θ)) ‘ θ) :
    IsForcingName (sparseCarrierCut ((forcingCodeP (woodinSparseStageCode θ)) ‘ θ) a) (p ‘ a) := by
  have hs := woodinSparseStageCode_sparse hΩ hAC hθ hp
  let := hs.1
  by_cases hd : a ∈ domain p
  · have ha := hs.2.1 a hd
    rcases mem_succ_iff.mp ha with he | ha
    · subst a
      exact woodinSparseStageCode_own_coordinate_isName hΩ hAC hθ hp
    · rcases woodinSourceIndex_cases ha with he | ⟨i, hi, he⟩
      · subst a
        exact False.elim (woodinSparseStageCode_no_zero hΩ hAC hθ hp hd)
      · subst a
        let := IsOrdinal.of_mem hi
        have hi' : i ∈ succ θ := mem_succ_iff.mpr (Or.inr hi)
        have hsub := subset_trans (IsOrdinal.toIsTransitive.transitive _ hi) hθ
        have hr := woodinSparseStageCode_restrict_mem hΩ hAC hθ hi hp
        have hn := woodinSparseStageCode_own_coordinate_isName hΩ hAC hsub hr
        rw [function_restrict_value_at (mem_succ_self _)] at hn
        apply hn.mono
        intro x hx
        obtain ⟨hx, hd⟩ := mem_sparseCarrierCut_iff.mp hx
        exact mem_sparseCarrierCut_iff.mpr ⟨woodinSparseStageCode_carrier_subset hΩ hAC hθ hi' x hx, hd⟩
  · rw [value_eq_empty_of_not_mem_domain hd]
    exact empty_forcingName _

end ZFVP
