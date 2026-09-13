import ZFVP.ModelTheory.WoodinRecodedRank
import ZFVP.ModelTheory.SparseNormalizedTwoStep
import ZFVP.SetTheory.WoodinSourceIndex
import ZFVP.ModelTheory.WoodinLimitCardinals

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem woodinSourceIndex_mem_of_mem {i δ : V} [IsOrdinal i]
    (hδ : ∀ β ∈ δ, succ β ∈ δ) (hi : i ∈ δ) : woodinSourceIndex i ∈ δ := by
  classical
  by_cases hn : i ∈ (ω : V)
  · rw [woodinSourceIndex_natural hn]
    exact hδ i hi
  · rwa [woodinSourceIndex_infinite hn]

theorem woodinSparseSuccessorCoordinate_mem {Ω k : V} [IsOrdinal k]
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hk : k ∈ Ω) :
    woodinSourceIndex (succ k) ∈ woodinNormalizedSuccessorCutoff k := by
  let := hΩ.inaccessible.1
  obtain ⟨hd, _⟩ := woodinNormalizedSuccessorCutoff_bounds hΩ hAC hk
  let := hd.1
  have hi := ((woodinIterationExit hΩ hAC).2.1 k hk).1.index_subset_cardinal k (mem_succ_self k)
  have hnew := woodinIterationActualCardinal_increasing hΩ hAC
    (hΩ.inaccessible.rankCriterion.2.2.1 k hk) (mem_succ_self k)
  rw [← woodinNormalizedSuccessorCutoff_actualCardinal hΩ hAC hk] at hnew
  let := IsOrdinal.of_mem hnew
  have hik : k ∈ woodinNormalizedSuccessorCutoff k := ordinal_mem_of_subset_mem hi hnew
  exact woodinSourceIndex_mem_of_mem hd.rankCriterion.2.2.1 (hd.rankCriterion.2.2.1 k hik)

theorem sparseNormalizedTwoStep_mem_larger_hierarchy {a A B top δ U ξ : V} [IsOrdinal δ] [IsOrdinal ξ]
    (hδ : ∀ β ∈ δ, succ β ∈ δ) (hξ : ∀ β ∈ ξ, succ β ∈ ξ)
    (hδξ : δ ∈ ξ) (ha : a ∈ hierarchy δ) (hA : A ⊆ hierarchy δ) :
    sparseNormalizedTwoStep a A B top δ U ∈ hierarchy ξ := by
  apply subset_mem_hierarchy_limit hξ ?_ (sparseNormalizedTwoStep_subset_hierarchy hδ ha hA)
  rw [mem_hierarchy_iff_rank_mem, rank_hierarchy]
  exact hδξ

theorem woodinRecodedSuccessorCutoff_eq {Ω k Q T m : V} [IsOrdinal k]
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hk : k ∈ Ω)
    (hm : ∀ i ∈ succ k, IsForcingIsomorphism
      ((forcingCodeP (woodinNormalizedPrefixCode (succ k))) ‘ i)
      ((forcingCodeR (woodinNormalizedPrefixCode (succ k))) ‘ i) (Q ‘ i) (T ‘ i) (m ‘ i))
    (hT : ∀ i ∈ succ k, IsForcingPreorder (Q ‘ i) (T ‘ i))
    (hQt : IsIterationTable (succ k) Q) (hTt : IsIterationTable (succ k) T) :
    let c := forcingRecodedCode (succ k) (woodinNormalizedPrefixCode (succ k)) Q T m
    woodinNormalizedSuccessorCutoff k = woodinPrefixCutoff ((forcingCodeP c) ‘ k)
      ((forcingCodeR c) ‘ k) ((forcingCodet c) ‘ k) ((kpair.π₂ (woodinIterationRec k)) ‘ k) := by
  let := hΩ.inaccessible.1
  let s := woodinNormalizedStageCode k
  let c := forcingRecodedCode (succ k) (woodinNormalizedPrefixCode (succ k)) Q T m
  have hsub : succ k ⊆ Ω := by
    intro i hi
    rcases mem_succ_iff.mp hi with rfl | hi
    · exact hk
    · exact IsOrdinal.toIsTransitive.mem_trans hi hk
  have hs := woodinNormalizedStageCode_valid hΩ hAC hk
  have hc := forcingRecoded_code (woodinNormalizedPrefixCode_valid hΩ hAC hsub) hm hT hQt hTt
  have hf := hm k (mem_succ_self k)
  rw [woodinNormalizedPrefix_successor hΩ hAC hk] at hf
  have hf' : IsForcingIsomorphism ((forcingCodeP s) ‘ k) ((forcingCodeR s) ‘ k)
      ((forcingCodeP c) ‘ k) ((forcingCodeR c) ‘ k) (m ‘ k) := by
    simpa only [s, c, forcingRecodedCode, forcingCodeP_code, forcingCodeR_code] using hf
  have hft : (m ‘ k) ‘ ((forcingCodet s) ‘ k) = (forcingCodet c) ‘ k := by
    simp only [s, c, forcingRecodedCode, forcingCodet_code, forcingRecodedTops_value (mem_succ_self k),
      woodinNormalizedPrefix_successor hΩ hAC hk]
  exact hf'.prefix_cutoff (hs.system.order.preorder k (mem_succ_self k))
    (hc.system.order.preorder k (mem_succ_self k)) (hs.system.tops.top k (mem_succ_self k))
    (hc.system.tops.top k (mem_succ_self k)) hft ((kpair.π₂ (woodinIterationRec k)) ‘ k)

end ZFVP
