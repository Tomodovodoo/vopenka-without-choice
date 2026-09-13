import ZFVP.ModelTheory.ClassForcingTowerSubsetStabilization
import ZFVP.ModelTheory.ClassForcingDenseChoices

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
namespace DefinableForcingTower
variable (T : DefinableForcingTower V)

/-- Begin the witness construction at a stage where the ground index set
has an ordinal enumeration and the matching dependent choice principle.
The prescribed initial class condition still projects into the generic. -/
theorem prepare_pretame_enumeration {G : Set V}
    (hG : IsGenericForDefinableDenseClasses T.Condition T.LE G)
    (henum : T.StageSetsHaveDCEnumerations hG) (I : V) {c : V} (hcG : c ∈ G) :
    ∃ i : V, ∃ hi : IsOrdinal i, ∃ α : V, ∃ hα : IsOrdinal α,
      c ∈ T.boundedConditions i ∧ T.projectCondition i c ∈ T.stageFilter G i ∧
      InternalDependentChoiceAt ((T.stageContext hG i).check α) ∧
      ∃ e : (T.stageContext hG i).Model,
        e ∈ ((T.stageContext hG i).check I) ^ ((T.stageContext hG i).check α) ∧
        range e = (T.stageContext hG i).check I := by
  obtain ⟨k, p, hk, hp, heq⟩ := hG.1.1 c hcG
  subst c
  let := hk
  obtain ⟨i, hi, hki, α, hα, hDC, e, he, hr⟩ := henum k ((T.stageContext hG k).check I)
  let := hi
  let := hα
  rw [T.stageInclusion_check hG hki] at he hr
  have hcond : T.Condition ⟨k, p⟩ₖ := (T.condition_pair k p).mpr ⟨hk, hp⟩
  have hproj := T.projectCondition_mem (i := i) hcond
  refine ⟨i, hi, α, hα, T.tagged_mem_boundedConditions hki hp, ?_, hDC, e, he, hr⟩
  exact ⟨hproj, hG.1.2.2.1 _ hcG _ ((T.condition_pair _ _).mpr ⟨hi, hproj⟩)
    (T.below_projectCondition hcond)⟩

end DefinableForcingTower
end ZFVP
