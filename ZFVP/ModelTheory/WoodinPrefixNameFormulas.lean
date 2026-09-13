import ZFVP.ModelTheory.WoodinPrefixSuccessor

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

def woodinPrefixPosetNameFormula : SetTheorySemisentence 6 :=
  f“Q P R o κ δ. !(formulaUniqueNameFormula totalWoodinCollapseFormula) Q P R
    (!assignmentPrependFormula (!(numeralFormula 1))
      (!assignmentPrependFormula (!(numeralFormula 0)) (!isEmpty) (!checkNameFormula o δ))
      (!checkNameFormula o κ))”

def reverseInclusionOrderNameFormula : SetTheorySemisentence 4 :=
  f“S P R Q. !(formulaUniqueNameFormula piOneReverseInclusionOrderFormula) S P R
    (!assignmentPrependFormula (!(numeralFormula 0)) (!isEmpty) Q)”

def forcedEmptyNameFormula : SetTheorySemisentence 3 :=
  f“t P R. !(formulaUniqueNameFormula isEmpty) t P R (!isEmpty)”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

instance woodinPrefixPosetNameFormula_defined :
    ℒₛₑₜ-function₅[V] woodinPrefixPosetName via woodinPrefixPosetNameFormula := by
  refine ⟨fun v ↦ ?_⟩
  simp [woodinPrefixPosetNameFormula, woodinPrefixPosetName, woodinCollapseName, standardTuple]

instance reverseInclusionOrderNameFormula_defined :
    ℒₛₑₜ-function₃[V] reverseInclusionOrderName via reverseInclusionOrderNameFormula := by
  refine ⟨fun v ↦ ?_⟩
  simp [reverseInclusionOrderNameFormula, reverseInclusionOrderName]

instance forcedEmptyNameFormula_defined :
    ℒₛₑₜ-function₂[V] forcedEmptyName via forcedEmptyNameFormula := by
  refine ⟨fun v ↦ ?_⟩
  simp [forcedEmptyNameFormula, forcedEmptyName]

instance forcedEmptyName_uniform_definable : ℒₛₑₜ-function₂[V] forcedEmptyName :=
  forcedEmptyNameFormula_defined.to_definable

end ZFVP
