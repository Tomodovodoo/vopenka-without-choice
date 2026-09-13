import ZFVP.ModelTheory.SuccessorForcingColumns
import ZFVP.SetTheory.ForcingLimitLiftColumns
import ZFVP.SetTheory.ForcingLiftSectionCompatibility

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem forcingLimit_sectionCompatibleColumn {θ P R π E L U C : V} [IsOrdinal θ]
    (h : IsSplitForcingSystem θ P π E) (hL : IsCoherentForcingLift θ P R π L)
    (hs : IsSectionCompatibleForcingLift θ P R π E L)
    (hU : ∀ i ∈ θ, P ‘ i ⊆ U) (hD : forcingDirectLimit θ P π E U ⊆ C) :
    IsSectionCompatibleLiftColumn θ P R π L (forcingLimitSectionColumn θ P π E)
      (forcingLimitLiftColumn C θ P π L) := by
  refine ⟨?_⟩
  intro i hi k hk hik a ha b hb hle
  have hq := (hL.lift i hi k hk hik a ha b hb hle).1
  rw [forcingLimitSectionColumn_value hk, forcingThreadSection_value ha,
    forcingLimitLiftColumn_value hi,
    forcingLimitLift_value (hD _ (forcingSectionThread_mem h hk ha hU)) hb,
    forcingThreadSection_value hq]
  exact forcingThreadSplice_section h hL hi hk hik ha hb hle hU
    (fun j hj hkj ↦ hs.compatible i hi k hk j hj hik hkj)

theorem successor_sectionCompatibleColumn {θ P R π E L k Q S t one : V}
    (h : IsSplitForcingSystem θ P π E) (hL : IsCoherentForcingLift θ P R π L)
    (hs : IsSectionCompatibleForcingLift θ P R π E L)
    (hk : k ∈ θ) (hmax : ∀ i ∈ θ, i ⊆ k)
    (hR : IsForcingPreorder (P ‘ k) (R ‘ k)) (htop : IsForcingTop (P ‘ k) (R ‘ k) one)
    (hQ : IsForcingIterand (P ‘ k) (R ‘ k) Q S t) :
    IsSectionCompatibleLiftColumn θ P R π L (successorSectionColumn θ P E k t)
      (successorLiftColumn θ (twoStepConditions (P ‘ k) (R ‘ k) Q t) P L k) := by
  refine ⟨?_⟩
  intro i hi j hj hij a ha b hb hle
  have hq := (hL.lift i hi j hj hij a ha b hb hle).1
  have ha' := twoStep_section_mem hR htop hQ (h.secMaps j hj k hk (hmax j hj) a ha)
  rw [successorSectionColumn_value hj ha, successorLiftColumn_value hi ha' hb,
    successorSectionColumn_value hj hq, successorForcingLift_section,
    hs.compatible i hi j hj k hk hij (hmax j hj) a ha b hb hle]

end ZFVP
