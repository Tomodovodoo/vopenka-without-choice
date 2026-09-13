import ZFVP.SetTheory.ForcingBoundThreadSections
import ZFVP.SetTheory.ForcingLimitBounds

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem limit_sectionCompatibleBoundColumn {θ P R π E B U C i I : V} [IsOrdinal θ]
    (h : IsSplitForcingSystem θ P π E) (m : IsFunctionalSplitForcingSystem θ P π E)
    (hB : IsCoherentForcingBound θ P R π B i I)
    (hc : IsSectionCompatibleForcingBound θ P R π E B i I)
    (hi : i ∈ θ) (hU : ∀ j ∈ θ, P ‘ j ⊆ U)
    (hD : forcingDirectLimit θ P π E U ⊆ C) :
    IsSectionCompatibleBoundColumn θ P R π B (forcingLimitSectionColumn θ P π E)
      (forcingLimitBound θ P π B i I C) i I := by
  constructor
  intro j hj hij f hf p hp hb
  have hm := mem_function_of_mem_function_of_subset (forcingThreadSection_maps h hj hU) hD
  rw [forcingLimitSectionColumn_value hj, forcingLimitBound_value (compose_function hf.1 hm) hp,
    forcingThreadSection_value (hB.bound j hj hij f hf p hp hb).1]
  exact forcingBoundThread_section h m hB hc hi hj hij hU hf hp hb

end ZFVP
