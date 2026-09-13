import ZFVP.ModelTheory.WoodinCollapseDisplacementName
import ZFVP.SetTheory.UniformFormulaName

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

def woodinCollapseDisplacementNameFormula : SetTheorySemisentence 7 :=
  f“n P R κ δ p q. !(formulaUniqueNameFormula woodinCollapseDisplacementFormula) n P R
    (!assignmentPrependFormula (!(numeralFormula 3))
      (!assignmentPrependFormula (!(numeralFormula 2))
        (!assignmentPrependFormula (!(numeralFormula 1))
          (!assignmentPrependFormula (!(numeralFormula 0)) (!isEmpty) q) p) δ) κ)”

def collapseConverseNameFormula : SetTheorySemisentence 4 :=
  f“n P R f. !(formulaUniqueNameFormula sparseConverseGraphFormula) n P R
    (!assignmentPrependFormula (!(numeralFormula 0)) (!isEmpty) f)”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

instance woodinCollapseDisplacementNameFormula_defined :
    Defined (fun v : Fin 7 → V ↦ v 0 =
      woodinCollapseDisplacementName (v 1) (v 2) (v 3) (v 4) (v 5) (v 6))
      woodinCollapseDisplacementNameFormula :=
  ⟨fun v ↦ by simp [woodinCollapseDisplacementNameFormula, woodinCollapseDisplacementName, standardTuple]⟩

instance woodinCollapseDisplacementName_uniform_definable :
    Language.DefinableFunction ℒₛₑₜ (fun v : Fin 6 → V ↦
      woodinCollapseDisplacementName (v 0) (v 1) (v 2) (v 3) (v 4) (v 5)) :=
  woodinCollapseDisplacementNameFormula_defined.to_definable

instance collapseConverseNameFormula_defined :
    ℒₛₑₜ-function₃[V] ZFVP.collapseConverseName via collapseConverseNameFormula :=
  ⟨fun v ↦ by simp [collapseConverseNameFormula, ZFVP.collapseConverseName, standardTuple]⟩

instance collapseConverseName_uniform_definable : ℒₛₑₜ-function₃[V] ZFVP.collapseConverseName :=
  collapseConverseNameFormula_defined.to_definable

end ZFVP
