import ZFVP.SetTheory.ClosedRankStages

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- The ranks attained by members of a transitive set form its rank,
with no well-ordering of the set required. -/
theorem transitive_rank_surjection {C : V} (hC : IsTransitive C) :
    ∃ r ∈ (rank C) ^ C, range r = rank C := by
  let r := definableGraph C rank (by definability)
  have hr : r ∈ (rank C) ^ C := definableGraph_mem_function_of_mapsTo _ _ _ _
    (fun x hx ↦ rank_mem hx)
  refine ⟨r, hr, subset_antisymm (range_subset_of_mem_function hr) ?_⟩
  intro α hα
  obtain ⟨x, hx, rfl⟩ := exists_mem_rank_eq hC hα
  rw [show range r = repl rank (by definability) C from range_definableGraph C rank (by definability)]
  exact (repl_spec _).mpr ⟨x, hx, rfl⟩

end ZFVP
