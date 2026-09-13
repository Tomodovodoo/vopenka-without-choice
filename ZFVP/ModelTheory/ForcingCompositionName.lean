import ZFVP.SetTheory.UniformFormulaName
import ZFVP.SetTheory.UniformFunctionOperations

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

def forcingCompositionNameFormula : SetTheorySemisentence 5 :=
  f“n P R f g. !(formulaUniqueNameFormula composeFormula) n P R
    (!assignmentPrependFormula (!(numeralFormula 1))
      (!assignmentPrependFormula (!(numeralFormula 0)) (!isEmpty) g) f)”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def forcingCompositionName (P R f g : V) : V :=
  formulaUniqueName P R composeFormula (standardTuple ![f, g])

instance forcingCompositionNameFormula_defined :
    ℒₛₑₜ-function₄[V] forcingCompositionName via forcingCompositionNameFormula :=
  ⟨fun v ↦ by simp [forcingCompositionNameFormula, forcingCompositionName, standardTuple]⟩

instance forcingCompositionName_definable : ℒₛₑₜ-function₄[V] forcingCompositionName :=
  forcingCompositionNameFormula_defined.to_definable

theorem forcingCompositionName_isName (P R f g : V) :
    IsForcingName P (forcingCompositionName P R f g) := formulaUniqueName_isName _ _ _ _

namespace ForcingContext

theorem forcingCompositionName_value (A : ForcingContext V) (f g : ForcingName A.P) :
    A.ofName ⟨forcingCompositionName A.P A.R f.val g.val, forcingCompositionName_isName _ _ _ _⟩ =
      compose (A.ofName f) (A.ofName g) := by
  change A.ofName (A.formulaName composeFormula ![f, g]) = _
  apply A.formulaName_value
  · intro x y hx hy
    simp at hx hy
    exact hx.trans hy.symm
  · simp

end ForcingContext
end ZFVP
