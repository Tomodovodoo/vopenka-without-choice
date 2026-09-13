import PalomarDCBridge.Vocabulary
import PalomarBridge.TheoremB
import ZFVP.ModelTheory.CountableCohenVopenkaConsistency

namespace PalomarDCBridge
open PalomarBridge LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {M : Type u} [SetStructure M] [Nonempty M] [M↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
local notation "mem" => (fun x y : M => x ∈ y)

/-- The independent DC definition agrees on arbitrary ZF membership models. -/
theorem dependentChoice_iff_internal : DependentChoice mem ↔ ZFVP.InternalDependentChoice M := by
  simp [DependentChoice, ZFVP.InternalDependentChoice, isNonempty_def]

/-- DC is exactly the sentence inserted in the source theory. -/
theorem dependentChoice_iff_sentence :
    DependentChoice mem ↔ M↓[ℒₛₑₜ] ⊧ ZFVP.dependentChoiceSentence := by
  rw [dependentChoice_iff_internal]
  simp [models_iff, Semiformula.Realize, ZFVP.dependentChoiceSentence,
    ZFVP.InternalDependentChoice]

/-- Failure of the transversal axiom is exactly failure of internal choice functions. -/
theorem failureOfChoice_iff_internal : FailureOfChoice mem ↔ ¬ ZFVP.InternalChoice M := by
  rw [FailureOfChoice, hasChoice_iff_models, ZFVP.internalChoice_iff_models_ac]

/-- The negated choice sentence has the same meaning as independent failure of AC. -/
theorem failureOfChoice_iff_sentence :
    FailureOfChoice mem ↔ M↓[ℒₛₑₜ] ⊧ ∼ZFVP.choiceFunctionSentence := by
  rw [failureOfChoice_iff_internal]
  simp [models_iff, Semiformula.Realize, ZFVP.choiceFunctionSentence, ZFVP.InternalChoice]

end PalomarDCBridge
