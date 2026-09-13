import ZFVP.ModelTheory.WoodinSparseOwnRankLower
import ZFVP.ModelTheory.WoodinSparseDirectRecovery

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem woodinSparseStageCode_rank_lower_below {Ω : V}
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) :
    ∀ θ ∈ Ω, ((kpair.π₂ (woodinIterationRec θ)) ‘ θ) ⊆
      rank ((forcingCodeP (woodinSparseStageCode θ)) ‘ θ) := by
  classical
  let := hΩ.inaccessible.1
  have hall := transfinite_induction
    (fun ξ : V ↦ ξ ∈ Ω → ((kpair.π₂ (woodinIterationRec ξ)) ‘ ξ) ⊆
      rank ((forcingCodeP (woodinSparseStageCode ξ)) ‘ ξ)) (by definability) ?_
  · intro θ hθ
    let := IsOrdinal.of_mem hθ
    exact hall (IsOrdinal.toOrdinal θ) hθ
  intro θ ih hθ
  have hsub := IsOrdinal.toIsTransitive.transitive _ hθ
  by_cases hz : (θ : V) = ∅
  · simpa only [hz] using woodinSparseStageCode_initial_rank_lower hΩ
  by_cases hs : (θ : V) = succ (⋃ˢ (θ : V))
  · have hm : ⋃ˢ (θ : V) ∈ (θ : V) :=
      (congrArg (fun x : V ↦ ⋃ˢ (θ : V) ∈ x) hs).mpr (mem_succ_self _)
    let := IsOrdinal.of_mem hm
    have hk : succ (⋃ˢ (θ : V)) ∈ Ω := hs ▸ hθ
    simpa only [← hs] using woodinSparseStageCode_successor_rank_lower hΩ hAC hk
  by_cases hn : IsChoicelessInaccessible (woodinLimitCardinal (woodinIterationCardinalPrefix (θ : V)))
  · rw [woodinDirect_stage_cardinal hΩ hAC hθ hz hs hn]
    apply woodinSparseStageCode_limit_rank_lower hΩ hAC hsub (ordinal_limit_of_not_successor hs)
    intro i hi
    let := IsOrdinal.of_mem hi
    exact ih (IsOrdinal.toOrdinal i) hi (hsub i hi)
  · exact woodinSparseStageCode_inverse_rank_lower hΩ hAC hθ hz hs hn

theorem woodinSparseStageCode_rank_lower {Ω θ : V} [IsOrdinal θ]
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω) :
    ((kpair.π₂ (woodinIterationRec θ)) ‘ θ) ⊆
      rank ((forcingCodeP (woodinSparseStageCode θ)) ‘ θ) := by
  let := hΩ.inaccessible.1
  rcases IsOrdinal.subset_iff.mp hθ with he | hi
  · subst Ω
    rw [woodinIteration_endpoint_cardinal hΩ hAC]
    exact woodinSparseStageCode_limit_rank_lower hΩ hAC (subset_refl θ)
      hΩ.inaccessible.rankCriterion.2.2.1 (woodinSparseStageCode_rank_lower_below hΩ hAC)
  · exact woodinSparseStageCode_rank_lower_below hΩ hAC θ hi

theorem woodinSparseStageCode_rank_eq {Ω θ : V} [IsOrdinal θ]
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω) :
    rank ((forcingCodeP (woodinSparseStageCode θ)) ‘ θ) =
      (kpair.π₂ (woodinIterationRec θ)) ‘ θ := by
  apply SetTheory.subset_antisymm
  · have hr := rank_mono (woodinSparseStageCode_own_bound hΩ hAC hθ)
    let := hΩ.inaccessible.1
    have hd : IsOrdinal ((kpair.π₂ (woodinIterationRec θ)) ‘ θ) := by
      rcases IsOrdinal.subset_iff.mp hθ with he | hi
      · subst Ω
        rw [woodinIteration_endpoint_cardinal hΩ hAC]
        infer_instance
      · exact (((woodinIterationExit hΩ hAC).2.1 θ hi).1.inaccessible θ (mem_succ_self _)).1
    simpa only [rank_hierarchy] using hr
  · exact woodinSparseStageCode_rank_lower hΩ hAC hθ

end ZFVP
