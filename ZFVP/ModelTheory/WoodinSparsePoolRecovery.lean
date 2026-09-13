import ZFVP.ModelTheory.SparseCoordinatePoolRecovery
import ZFVP.ModelTheory.WoodinSparseOwnCutoffs

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable {Ω θ : V} [IsOrdinal θ]

theorem woodinSparseInitial_pool_recovery :
    sparseCoordinatePool (woodinSparseInitialCarrier : V) (succ ∅) =
      normalizedNamePool ({∅} : V) (({∅} : V) ×ˢ {∅}) ∅
        (woodinPrefixCutoff ({∅} : V) (({∅} : V) ×ˢ {∅}) ∅ woodinSeedCardinal)
        (saturatedWoodinPrefixPosetName ({∅} : V) (({∅} : V) ×ˢ {∅}) ∅ woodinSeedCardinal
          (woodinPrefixCutoff ({∅} : V) (({∅} : V) ×ˢ {∅}) ∅ woodinSeedCardinal)) := by
  apply sparsePairCarrier_pool_recovery
  · intro p hp
    have he : p = (∅ : V) := by simpa using hp
    subst p
    exact isSparseFunctionOn_empty _
  · exact ⟨∅, by simp⟩

theorem woodinSparseStageCode_pool_restriction
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω)
    {i a : V} (hi : i ∈ succ θ) (ha : a ∈ succ (woodinSourceIndex i)) :
    sparseCoordinatePool ((forcingCodeP (woodinSparseStageCode i)) ‘ i) a =
      sparseCoordinatePool ((forcingCodeP (woodinSparseStageCode θ)) ‘ θ) a := by
  let := IsOrdinal.of_mem hi
  rcases mem_succ_iff.mp hi with he | hi
  · subst i
    rfl
  apply sparseCoordinatePool_restriction
    (woodinSparseStageCode_carrier_subset hΩ hAC hθ (mem_succ_iff.mpr (Or.inr hi)))
    (fun _ hp ↦ (woodinSparseStageCode_sparse hΩ hAC hθ hp).1) ?_ ha
  intro p hp
  have hh := (woodinSparseStageCode_valid hΩ hAC hθ).system.split.projMaps
    i (mem_succ_iff.mpr (Or.inr hi)) θ (mem_succ_self θ)
    (IsOrdinal.toIsTransitive.transitive _ hi) p hp
  rwa [woodinSparseStageCode_projection hΩ hAC hθ hi hp,
    (woodinSparseStage_old_row (mem_succ_iff.mpr (Or.inr hi))).1] at hh

theorem woodinSparseStageCode_successor_pool_recovery {k : V} [IsOrdinal k]
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hk : succ k ⊆ Ω) :
    sparseCoordinatePool ((forcingCodeP (woodinSparseStageCode (succ k))) ‘ (succ k))
      (woodinSourceIndex (succ k)) = woodinSparseSuccessorPool k (woodinSparsePrefixCode (succ k)) := by
  rw [(woodinSparseStageCode_successor k).1]
  apply sparsePairCarrier_pool_recovery
  · intro p hp
    rw [woodinSourceIndex_successor]
    exact woodinSparsePrefixCode_sparse hΩ hAC hk (mem_succ_self k) hp
  · exact ⟨_, ((woodinSparsePrefixCode_valid hΩ hAC hk).system.tops.top k (mem_succ_self k)).1⟩

theorem woodinSparseStageCode_inverse_pool_recovery
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω)
    (h0 : θ ≠ ∅) (hlim : θ ≠ succ (⋃ˢ θ))
    (hn : ¬IsChoicelessInaccessible (woodinLimitCardinal (woodinIterationCardinalPrefix θ))) :
    sparseCoordinatePool ((forcingCodeP (woodinSparseStageCode θ)) ‘ θ) θ =
      woodinSparseInversePool θ (woodinSparsePrefixCode θ) := by
  rw [(woodinSparseStageCode_inverse h0 hlim hn).1]
  apply sparsePairCarrier_pool_recovery
  · intro p hp
    exact ((mem_woodinSparseInverseBase_iff (woodinSparsePrefixCode_valid hΩ hAC hθ)).mp hp).1
  · have hz : (∅ : V) ∈ θ := (IsOrdinal.subset_iff.mp (empty_subset θ)).resolve_left (fun he ↦ h0 he.symm)
    exact ⟨∅, (woodinSparsePrefix_inverse_base_laws hΩ hAC hθ hz
      (ordinal_limit_of_not_successor hlim)).2.1⟩

theorem woodinSparseStageCode_earlier_successor_pool_recovery {k : V} [IsOrdinal k]
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω)
    (hk : succ k ∈ succ θ) :
    sparseCoordinatePool ((forcingCodeP (woodinSparseStageCode θ)) ‘ θ) (woodinSourceIndex (succ k)) =
      woodinSparseSuccessorPool k (woodinSparsePrefixCode (succ k)) := by
  rw [← woodinSparseStageCode_pool_restriction hΩ hAC hθ hk (mem_succ_self _)]
  exact woodinSparseStageCode_successor_pool_recovery hΩ hAC
    (subset_trans (IsOrdinal.subset_iff.mpr (mem_succ_iff.mp hk)) hθ)

theorem woodinSparseStageCode_earlier_inverse_pool_recovery {i : V}
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω)
    (hi : i ∈ succ θ) (h0 : i ≠ ∅) (hlim : i ≠ succ (⋃ˢ i))
    (hn : ¬IsChoicelessInaccessible (woodinLimitCardinal (woodinIterationCardinalPrefix i))) :
    sparseCoordinatePool ((forcingCodeP (woodinSparseStageCode θ)) ‘ θ) i =
      woodinSparseInversePool i (woodinSparsePrefixCode i) := by
  let := IsOrdinal.of_mem hi
  have hz : (∅ : V) ∈ i := (IsOrdinal.subset_iff.mp (empty_subset i)).resolve_left (fun he ↦ h0 he.symm)
  have ha : i ∈ succ (woodinSourceIndex i) := by
    rw [woodinSourceIndex_limit i hz (ordinal_limit_of_not_successor hlim)]
    exact mem_succ_self i
  rw [← woodinSparseStageCode_pool_restriction hΩ hAC hθ hi ha]
  exact woodinSparseStageCode_inverse_pool_recovery hΩ hAC
    (subset_trans (IsOrdinal.subset_iff.mpr (mem_succ_iff.mp hi)) hθ) h0 hlim hn

end ZFVP
