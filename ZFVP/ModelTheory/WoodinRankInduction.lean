import ZFVP.ModelTheory.WoodinRankLimit

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

instance woodinRankStage_definable : ℒₛₑₜ-relation₃[V] WoodinRankStage :=
  woodinRankStageFormula_defined.to_definable

/-- The rank invariant holds at every actual recursive stage below the endpoint. -/
theorem woodinIteration_rankStages_countable [Countable V] {δ : V}
    (hδ : IsWoodinSupercompact δ) :
    ∀ θ ∈ δ, WoodinRankStage θ (kpair.π₁ (woodinIterationRec θ))
      (kpair.π₂ (woodinIterationRec θ)) := by
  classical
  let := hδ.inaccessible.1
  have hall := transfinite_induction
    (fun ξ : V ↦ ξ ∈ δ → WoodinRankStage ξ (kpair.π₁ (woodinIterationRec ξ))
      (kpair.π₂ (woodinIterationRec ξ))) (by definability) ?_
  · intro θ hθ
    let := IsOrdinal.of_mem hθ
    exact hall (IsOrdinal.toOrdinal θ) hθ
  intro θ ih hθ
  have hr : ∀ i ∈ (θ : V), WoodinRankStage i (kpair.π₁ (woodinIterationRec i))
      (kpair.π₂ (woodinIterationRec i)) := by
    intro i hi
    let := IsOrdinal.of_mem hi
    exact ih (IsOrdinal.toOrdinal i) hi (IsOrdinal.toIsTransitive.mem_trans hi hθ)
  by_cases he : (θ : V) = succ (⋃ˢ (θ : V))
  · have hk : ⋃ˢ (θ : V) ∈ (θ : V) :=
      (congrArg (fun x : V ↦ ⋃ˢ (θ : V) ∈ x) he).mpr (mem_succ_self (⋃ˢ (θ : V)))
    let := IsOrdinal.of_mem hk
    have hs : ∀ j ∈ succ (⋃ˢ (θ : V)), IsWoodinIteration δ (succ j)
        (kpair.π₁ (woodinIterationRec j)) (kpair.π₂ (woodinIterationRec j)) := by
      intro j hj
      exact (woodinIteration_stages_countable hδ j
        (IsOrdinal.toIsTransitive.mem_trans (he.symm ▸ hj) hθ)).1
    have hn := woodinIterationRec_rankStage_successor hδ hs (hr _ hk)
    simpa only [← he] using hn
  · exact woodinIterationRec_rankStage_limit hδ hθ (ordinal_limit_of_not_successor he) hr

end ZFVP
