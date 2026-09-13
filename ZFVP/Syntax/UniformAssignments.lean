import ZFVP.Syntax.Assignments
import ZFVP.SetTheory.UniformNumerals

/-! Shared parameter-free formulas for extending bound assignments. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def prependValueFormula : SetTheorySemisentence 4 :=
  f“y b x i. (i = !(numeralFormula 0) ∧ y = x) ∨
    (i ≠ !(numeralFormula 0) ∧ y = !value.dfn b (!sUnion.dfn i))”

def assignmentPrependFormula : SetTheorySemisentence 4 :=
  f“B n b x. ∀ p, p ∈ B ↔ ∃ i ∈ !succ.dfn n, p = !kpair.dfn i (!prependValueFormula b x i)”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

instance prependValueFormula_defined : ℒₛₑₜ-function₃[V] prependValue via prependValueFormula :=
  ⟨fun v ↦ by
    by_cases hi : v 3 = 0 <;> simp [prependValueFormula, prependValue, hi]⟩

instance assignmentPrependFormula_defined : ℒₛₑₜ-function₃[V] assignmentPrepend via assignmentPrependFormula :=
  ⟨fun v ↦ by
    change assignmentPrependFormula.Evalb v ↔ v 0 = assignmentPrepend (v 1) (v 2) (v 3)
    rw [mem_ext_iff]
    simp [assignmentPrependFormula, assignmentPrepend, mem_definableGraph_iff]⟩

end ZFVP
