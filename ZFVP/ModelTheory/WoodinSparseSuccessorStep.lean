import ZFVP.ModelTheory.WoodinSparseHistoryLaws
import ZFVP.ModelTheory.WoodinSparseSuccessorRank
import ZFVP.ModelTheory.WoodinSparseSuccessorValues

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem woodinSparseInitialRow_correct {Ω : V} (hΩ : IsWoodinSupercompact Ω) :
    IsWoodinSparseRow (∅ : V) woodinSparseRecodingInitialRow := by
  simp only [IsWoodinSparseRow, IsWoodinRecodedRow, woodinSparseRecodingInitialRow,
    kpair.π₁_kpair, kpair.π₂_kpair]
  refine ⟨⟨woodinSparseInitialMap_isomorphism hΩ, woodinSparseInitial_preorder hΩ,
    fun ξ hξ hc ↦ woodinSparseInitial_small hΩ hξ hc⟩,
    fun p hp ↦ woodinSparseInitial_sparse hp, woodinSparseInitialMap_top hΩ, ?_, ?_⟩
  all_goals intro i hi; exact (not_mem_empty hi).elim

theorem woodinSparseSuccessorRow_correct {Ω k : V} [IsOrdinal k]
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hk : succ k ∈ Ω)
    (ih : ∀ i ∈ succ k, IsWoodinSparseRow i (woodinSparseRecodingRec i)) :
    IsWoodinSparseRow (succ k) (woodinSparseRecodingSuccessorRow k
      (forcingRecodedCode (succ k) (woodinNormalizedPrefixCode (succ k))
        (woodinRecodingCarriers (woodinSparseRecodingHistory (succ k)))
        (woodinRecodingOrders (woodinSparseRecodingHistory (succ k)))
        (woodinRecodingMaps (woodinSparseRecodingHistory (succ k))))
      (woodinRecodingMaps (woodinSparseRecodingHistory (succ k)))) := by
  let := hΩ.inaccessible.1
  have hsub := IsOrdinal.toIsTransitive.transitive _ hk
  have hkΩ := hsub k (mem_succ_self k)
  let Q := woodinRecodingCarriers (woodinSparseRecodingHistory (succ k))
  let T := woodinRecodingOrders (woodinSparseRecodingHistory (succ k))
  let m := woodinRecodingMaps (woodinSparseRecodingHistory (succ k))
  let c := forcingRecodedCode (succ k) (woodinNormalizedPrefixCode (succ k)) Q T m
  have hQt : IsIterationTable (succ k) Q := (woodinSparseRecodingHistory_tables (succ k)).1
  have hTt : IsIterationTable (succ k) T := (woodinSparseRecodingHistory_tables (succ k)).2.1
  have hm := woodinSparseHistory_family hΩ hAC hsub ih
  have hT : ∀ i ∈ succ k, IsForcingPreorder (Q ‘ i) (T ‘ i) :=
    fun i hi ↦ woodinSparseHistory_preorder ih hi
  have hd := (woodinNormalizedSuccessorCutoff_bounds hΩ hAC hkΩ).1
  have hQrank : Q ‘ k ∈ hierarchy (woodinNormalizedSuccessorCutoff k) := by
    apply woodinSparseHistory_small ih (mem_succ_self k) hd
    rw [woodinNormalizedSuccessorCutoff_actualCardinal hΩ hAC hkΩ]
    exact woodinIterationActualCardinal_increasing hΩ hAC hk (mem_succ_self k)
  have hsp : ∀ p ∈ Q ‘ k, IsSparseFunctionOn (woodinSourceIndex (succ k)) p := by
    intro p hp
    rw [woodinSourceIndex_successor]
    exact woodinSparseHistory_sparse ih (mem_succ_self k) hp
  have hf := woodinSparseSuccessorMap_isomorphism hΩ hAC hkΩ hm hT hQt hTt hQrank hsp
  have hs := woodinNormalizedStageCode_valid hΩ hAC hk
  change IsWoodinSparseRow (succ k) (woodinSparseRecodingSuccessorRow k c m)
  simp only [IsWoodinSparseRow, IsWoodinRecodedRow, woodinSparseRecodingSuccessorRow,
    kpair.π₁_kpair, kpair.π₂_kpair]
  refine ⟨⟨hf, hf.target_preorder (hs.system.order.preorder _ (mem_succ_self _))
    (forcingPullbackOrder_subset _ _ _), ?_⟩, ?_, ?_, ?_, ?_⟩
  · intro ξ hξ hc
    exact woodinSparseSuccessorCarrier_small hΩ hAC hkΩ hm hT hQt hTt hQrank hξ hc
  · intro p hp
    exact (mem_sparsePairCarrier_iff.mp hp).1
  · apply woodinSparseSuccessorMap_top hΩ hAC hkΩ hm hT hQt hTt hQrank hsp
    change ((woodinRecodingMaps (woodinSparseRecodingHistory (succ k))) ‘ k) ‘ _ = ∅
    rw [(woodinSparseRecodingHistory_values (mem_succ_self k)).2.2]
    exact (ih k (mem_succ_self k)).2.2.1
  · intro i hi p hp
    have he := woodinSparseSuccessorMap_projection hΩ hAC hkΩ hm hT hQt hTt hQrank hsp hi hp
      (fun i hi j hj hij p hp ↦ woodinSparseHistory_projection hΩ hAC hsub ih hi hj hij hp)
    rw [(woodinSparseRecodingHistory_values hi).2.2] at he
    exact he
  · intro i hi p hp
    have hpD : p ∈ (forcingCodeP (woodinNormalizedStageCode k)) ‘ i := by
      rwa [woodinNormalizedStage_successor_old_carrier hΩ hAC hkΩ hi] at hp
    rw [woodinSparseSuccessorMap_section hΩ hAC hkΩ hm hT hQt hTt hQrank hsp hi hpD]
    have hpN : p ∈ (forcingCodeP (woodinNormalizedPrefixCode (succ k))) ‘ i := by
      rwa [woodinNormalizedPrefix_successor hΩ hAC hkΩ]
    have hik : i ⊆ k := by
      rcases mem_succ_iff.mp hi with rfl | hi
      · exact subset_refl _
      · exact IsOrdinal.toIsTransitive.transitive _ hi
    have he := forcingRecodedSections_image (woodinNormalizedPrefixCode_valid hΩ hAC hsub) hm
      hi (mem_succ_self k) hik hpN
    rw [woodinSparseHistory_section hΩ hAC hsub ih hi (mem_succ_self k) hik
      (function_value_mem (hm i hi).1 hpN), woodinNormalizedPrefix_successor hΩ hAC hkΩ,
      (woodinSparseRecodingHistory_values hi).2.2] at he
    exact he.symm

end ZFVP
