import ZFVP.SetTheory.ForcingMapExtension
import ZFVP.SetTheory.ForcingLimitColumns
import ZFVP.ModelTheory.SuccessorForcingColumns

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem forcingLimit_functionalColumn {θ P π E U C : V} [IsOrdinal θ]
    (h : IsSplitForcingSystem θ P π E) (hU : ∀ i ∈ θ, P ‘ i ⊆ U)
    (hD : forcingDirectLimit θ P π E U ⊆ C) (hI : C ⊆ forcingInverseLimit θ P π U) :
    IsFunctionalSplitForcingColumn θ P C
      (forcingLimitProjectionColumn θ C) (forcingLimitSectionColumn θ P π E) := by
  constructor
  · intro i hi
    rw [forcingLimitProjectionColumn_value hi]
    apply definableGraph_mem_function_of_mapsTo
    intro f hf
    exact ((mem_forcingInverseLimit_iff _ _ _ _ _).mp (hI f hf)).2.1 i hi
  · intro i hi
    rw [forcingLimitSectionColumn_value hi]
    apply definableGraph_mem_function_of_mapsTo
    intro p hp
    exact hD _ (forcingSectionThread_mem h hi hp hU)

theorem successor_functionalColumn {θ P R π E k Q S t one : V}
    (h : IsSplitForcingSystem θ P π E) (hk : k ∈ θ) (hmax : ∀ i ∈ θ, i ⊆ k)
    (hR : IsForcingPreorder (P ‘ k) (R ‘ k)) (htop : IsForcingTop (P ‘ k) (R ‘ k) one)
    (hQ : IsForcingIterand (P ‘ k) (R ‘ k) Q S t) :
    IsFunctionalSplitForcingColumn θ P (twoStepConditions (P ‘ k) (R ‘ k) Q t)
      (successorProjectionColumn θ (twoStepConditions (P ‘ k) (R ‘ k) Q t) π k)
      (successorSectionColumn θ P E k t) := by
  have c := successor_splitColumn h hk hmax hR htop hQ
  constructor
  · intro i hi
    rw [successorProjectionColumn, value_definableGraph _ _ _ hi]
    apply definableGraph_mem_function_of_mapsTo
    intro a ha
    have hc := c.projMaps i hi a ha
    rwa [successorProjectionColumn_value hi ha] at hc
  · intro i hi
    rw [successorSectionColumn, value_definableGraph _ _ _ hi]
    apply definableGraph_mem_function_of_mapsTo
    intro p hp
    have hc := c.secMaps i hi p hp
    rwa [successorSectionColumn_value hi hp] at hc

end ZFVP
