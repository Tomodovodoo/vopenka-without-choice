import ZFVP.ModelTheory.WoodinLocalStagePresentation
import ZFVP.ModelTheory.WoodinEndpointStageConditions
import ZFVP.SetTheory.FiniteCodingClosure

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- This is an external restriction of a definable class to the rank cut;
no absoluteness of the recursion formula is asserted. -/
theorem woodinIteration_stage_conditions_local_rank {δ z : V}
    (hδ : IsWoodinSupercompact δ) (hAC : ¬InternalChoice V) :
    z ∈ forcingStageConditions δ (forcingCodeP (woodinIterationPrefix δ))
      (forcingCodeUniverse (woodinIterationPrefix δ)) ↔
      z ∈ hierarchy δ ∧ IsWoodinLocalStageCondition z := by
  let := hδ.inaccessible.1
  have hs := fun i hi ↦ ((woodinIterationExit hδ hAC).2.1 i hi).1
  constructor
  · intro hz
    exact ⟨woodinIteration_stage_conditions_subset hδ hAC z hz,
      ((woodinStageConditions_iff_local hs).mp hz).1⟩
  · rintro ⟨hz, hc⟩
    apply (woodinStageConditions_iff_local hs).mpr
    refine ⟨hc, ?_⟩
    obtain ⟨i, p, hi, _, rfl⟩ := hc
    let := hi
    let := hierarchy_transitive δ
    simpa only [kpair.π₁_kpair] using
      (ordinal_mem_hierarchy_iff.mp (kpair_components_mem_transitive hz).1 : i ∈ δ)

end ZFVP
