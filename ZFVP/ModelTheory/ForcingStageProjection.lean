import ZFVP.ModelTheory.ForcingProjection
import ZFVP.SetTheory.ForcingPullbackOrder
import ZFVP.SetTheory.ForcingStageThreadMap

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem forcingPullbackOrder_projection {P R Q π : V}
    (hπ : π ∈ P ^ Q) (hs : ∀ f ∈ P, ∃ z ∈ Q, π ‘ z = f) :
    IsForcingProjection P R Q (forcingPullbackOrder Q R π) π := by
  refine ⟨hπ, ?_, ?_⟩
  · intro p _ q _ hpq
    exact ((mem_forcingPullbackOrder_iff _ _ _ _ _).mp hpq).2.2
  · intro q hq p hp hpq
    obtain ⟨z, hz, he⟩ := hs p hp
    refine ⟨z, hz, (mem_forcingPullbackOrder_iff _ _ _ _ _).mpr ⟨hz, hq, ?_⟩, he⟩
    rwa [he]

/-- Stage codes project onto the thread presentation with exact stronger lifts. -/
theorem forcingStageThreadMap_projection {θ P π E U R : V} [IsOrdinal θ]
    (h : IsSplitForcingSystem θ P π E) (hU : ∀ i ∈ θ, P ‘ i ⊆ U) :
    IsForcingProjection (forcingDirectLimit θ P π E U) R
      (forcingStageConditions θ P U)
      (forcingPullbackOrder (forcingStageConditions θ P U) R (forcingStageThreadMap θ P π E U))
      (forcingStageThreadMap θ P π E U) :=
  forcingPullbackOrder_projection (forcingStageThreadMap_maps h hU)
    (fun _ hf ↦ forcingStageThreadMap_surjective h hU hf)

/-- Pulling back the coordinatewise thread order makes the stage codes a preorder. -/
theorem forcingStageConditions_preorder {θ P R π E U : V} [IsOrdinal θ]
    (h : IsSplitForcingSystem θ P π E) (hU : ∀ i ∈ θ, P ‘ i ⊆ U)
    (hR : ∀ i ∈ θ, IsForcingPreorder (P ‘ i) (R ‘ i)) :
    IsForcingPreorder (forcingStageConditions θ P U)
      (forcingPullbackOrder (forcingStageConditions θ P U)
        (forcingThreadOrder θ R (forcingDirectLimit θ P π E U))
        (forcingStageThreadMap θ P π E U)) :=
  forcingPullbackOrder_preorder (forcingDirectLimit_preorder hR)
    (forcingStageThreadMap_maps h hU)

end ZFVP
