import ZFVP.ModelTheory.ForcingHartogsName
import ZFVP.SetTheory.UniformFormulaName

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

def hartogsNumberNameFormula : SetTheorySemisentence 4 :=
  f“κ P R τ. !(formulaUniqueNameFormula hartogsNumberFormula) κ P R
    (!assignmentPrependFormula (!(numeralFormula 0)) (!isEmpty) τ)”

def namedUnaryForcingFormula (φ : SetTheorySemisentence 1) : SetTheorySemisentence 4 :=
  f“P R p τ. !(forcingTruthFormula φ) p P R
    (!assignmentPrependFormula (!(numeralFormula 0)) (!isEmpty) τ)”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

instance hartogsNumberNameFormula_defined :
    ℒₛₑₜ-function₃[V] hartogsNumberName via hartogsNumberNameFormula :=
  ⟨fun v ↦ by simp [hartogsNumberNameFormula, hartogsNumberName]⟩

instance hartogsNumberName_uniform_definable : ℒₛₑₜ-function₃[V] hartogsNumberName :=
  hartogsNumberNameFormula_defined.to_definable

instance namedUnaryForcingFormula_defined (φ : SetTheorySemisentence 1) :
    Defined (fun v : Fin 4 → V ↦ v 2 ∈ forcingFormula (v 0) (v 1) φ (standardTuple ![v 3]))
      (namedUnaryForcingFormula φ) :=
  ⟨fun v ↦ by simp [namedUnaryForcingFormula, standardTuple]⟩

end ZFVP
