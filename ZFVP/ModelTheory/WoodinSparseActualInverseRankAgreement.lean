import ZFVP.ModelTheory.RankSparseCompletedInverse
import ZFVP.ModelTheory.WoodinSparseRawInverseDC

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem woodinSparsePrefix_inverse_rankInputs {Ω θ : V} [IsOrdinal θ]
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ∈ Ω)
    (hzero : θ ≠ ∅) (hlim : ∀ i ∈ θ, succ i ∈ θ)
    (hn : ¬IsChoicelessInaccessible (woodinLimitCardinal (woodinIterationCardinalPrefix θ))) :
    SparseInverseRankForcingInputs θ (woodinSparsePrefixCode θ) := by
  let := hΩ.inaccessible.1
  have hsub := IsOrdinal.toIsTransitive.transitive _ hθ
  have h0 : (∅ : V) ∈ θ := (IsOrdinal.subset_iff.mp (empty_subset θ)).resolve_left (fun he ↦ hzero he.symm)
  have hs := woodinIterationPrefix_of_stages
    (fun i hi ↦ ((woodinIterationExit hΩ hAC).2.1 i (hsub i hi)).1)
  have hl := woodinSparseRawInverse_laws hΩ hAC hsub h0 hlim
  have hf := woodinSparseRawInverseDC hΩ hAC hθ hzero hlim hn
  refine ⟨hl.1, hl.2, hs.limitCardinal_ordinal, ?_, ?_, ?_⟩
  · intro κ hκ hγκ
    let := hκ.1
    let := hs.limitCardinal_ordinal
    apply woodinSparseInverseBase_small (woodinSparsePrefixCode_valid hΩ hAC hsub) hκ
      (ordinal_mem_hierarchy_iff.mpr (ordinal_mem_of_subset_mem (hs.index_subset_limit hlim) hγκ))
    intro i hi
    apply woodinSparsePrefixCode_small hΩ hAC hsub hi hκ
    have hm := hs.cardinal_mem_limit hlim hi
    rw [woodinIterationCardinalPrefix_value hΩ hAC hsub hi] at hm
    exact IsOrdinal.toIsTransitive.mem_trans hm hγκ
  · intro p hp
    have hh := hf p hp
    rw [woodinStageCardinalFormula, forcingFormula_and, mem_inter_iff] at hh
    exact hh.1
  · intro p hp
    have hh := hf p hp
    rw [woodinStageCardinalFormula, forcingFormula_and, mem_inter_iff] at hh
    exact hh.2

namespace TransitiveZF
variable {Ω : V} [IsOrdinal Ω] [Nonempty (SetDomain (hierarchy Ω))]
  [(SetDomain (hierarchy Ω))↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem woodinSparseCompletedInverse_val_of_actual_prefix (hΩ : IsWoodinSupercompact Ω)
    (hAC : ¬InternalChoice V) (θ c : SetDomain (hierarchy Ω)) [IsOrdinal θ]
    (hc : c.val = woodinSparsePrefixCode θ.val)
    (hzero : θ.val ≠ ∅) (hlim : ∀ i ∈ θ.val, succ i ∈ θ.val)
    (hn : ¬IsChoicelessInaccessible (woodinLimitCardinal (woodinIterationCardinalPrefix θ.val))) :
    (woodinSparseInverseCutoff θ c).val = woodinSparseInverseCutoff θ.val c.val ∧
    (woodinSparseInversePool θ c).val = woodinSparseInversePool θ.val c.val ∧
    (woodinSparseCompletedInverseCarrier θ c).val = woodinSparseCompletedInverseCarrier θ.val c.val ∧
    (woodinSparseCompletedInverseOrder θ c).val = woodinSparseCompletedInverseOrder θ.val c.val := by
  let := hierarchy_transitive Ω
  let := (ordinal_iff (hierarchy Ω) θ).mp (inferInstance : IsOrdinal θ)
  apply woodinSparseCompletedInverse_val_endpoint hΩ hAC θ c
  rw [hc]
  exact woodinSparsePrefix_inverse_rankInputs hΩ hAC
    (ordinal_mem_hierarchy_iff.mp θ.property) hzero hlim hn

end TransitiveZF
end ZFVP
