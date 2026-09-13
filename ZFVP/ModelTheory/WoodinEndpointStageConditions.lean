import ZFVP.ModelTheory.WoodinEndpointFiltration
import ZFVP.SetTheory.ForcingStageConditions

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- The stage-code carrier for the actual constructed endpoint lies in its rank cut. -/
theorem woodinIteration_stage_conditions_subset {δ : V} (hδ : IsWoodinSupercompact δ)
    (hAC : ¬InternalChoice V) :
    forcingStageConditions δ (forcingCodeP (woodinIterationPrefix δ))
      (forcingCodeUniverse (woodinIterationPrefix δ)) ⊆ hierarchy δ := by
  let := hδ.inaccessible.1
  have h := (woodinIterationExit hδ hAC).2.2.1
  apply forcingStageConditions_subset_hierarchy hδ.inaccessible.rankCriterion.2.2.1
  intro i hi p hp
  have hb : woodinStageCardinal (woodinIterationStage (woodinIterationPrefix δ)
      (woodinIterationCardinalPrefix δ) i) ∈ δ := by
    simpa only [woodinIterationStage, woodinStageCardinal_code] using h.bounded i hi
  have hs := h.small i hi δ hδ.inaccessible hb
  have hs' : (forcingCodeP (woodinIterationPrefix δ)) ‘ i ∈ hierarchy δ := by
    simpa only [woodinIterationStage, woodinStagePoset_code] using hs
  exact (hierarchy_transitive δ).mem_trans hp hs'

end ZFVP
