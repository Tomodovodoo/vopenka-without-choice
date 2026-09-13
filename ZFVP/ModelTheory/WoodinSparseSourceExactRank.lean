import ZFVP.ModelTheory.WoodinSparseExactRank
import ZFVP.ModelTheory.WoodinSparseSourceCode
import ZFVP.ModelTheory.WoodinSparseQuotientInputs

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable {Ω θ : V} [IsOrdinal θ]

theorem woodinSparseSourceStageCode_rank_eq_at_sourceIndex
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω)
    {i : V} (hi : i ∈ succ θ) :
    rank ((forcingCodeP (woodinSparseSourceStageCode θ)) ‘ (woodinSourceIndex i)) =
      (woodinSparseSourceStageCardinals θ) ‘ (woodinSourceIndex i) := by
  let := IsOrdinal.of_mem hi
  rw [(woodinSparseSourceStageCode_row hi).1, (woodinSparseStage_old_row hi).1,
    woodinSparseSourceStageCardinals_value hΩ hAC hθ hi]
  apply woodinSparseStageCode_rank_eq hΩ hAC
  exact subset_trans (IsOrdinal.subset_iff.mpr (mem_succ_iff.mp hi)) hθ

theorem woodinSparseSourceStageCode_rank_eq_positive
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hθ : θ ⊆ Ω)
    {i : V} (hi : i ∈ succ (woodinSourceIndex θ)) (hne : i ≠ ∅) :
    rank ((forcingCodeP (woodinSparseSourceStageCode θ)) ‘ i) =
      (woodinSparseSourceStageCardinals θ) ‘ i := by
  rw [← woodinSourceIndex_successor] at hi
  rcases woodinSourceIndex_cases hi with hz | ⟨j, hj, rfl⟩
  · exact (hne hz).elim
  · exact woodinSparseSourceStageCode_rank_eq_at_sourceIndex hΩ hAC hθ hj

theorem woodinSparseSourceStageCode_seed_rank :
    rank ((forcingCodeP (woodinSparseSourceStageCode θ)) ‘ ∅) = (1 : V) := by
  rw [woodinSparseSourceStageCode_seed.1, rank_singleton, rank_empty]
  rfl

theorem woodinSparseSourceStageCode_endpoint_rank (hΩ : IsWoodinSupercompact Ω)
    (hAC : ¬InternalChoice V) :
    rank ((forcingCodeP (woodinSparseSourceStageCode Ω)) ‘ (woodinSourceIndex Ω)) = Ω := by
  let := hΩ.inaccessible.1
  rw [woodinSparseSourceStageCode_rank_eq_at_sourceIndex hΩ hAC (subset_refl Ω) (mem_succ_self Ω),
    woodinSparseSourceStageCardinals_value hΩ hAC (subset_refl Ω) (mem_succ_self Ω),
    woodinIteration_endpoint_cardinal hΩ hAC]

end ZFVP
