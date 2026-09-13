import ZFVP.SetTheory.UniformRank
import ZFVP.Syntax.UniformAssignments
import ZFVP.Syntax.StandardTuples

/-! Elementary maps preserve operations given by the same parameter-free formula. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

namespace ElementaryMap

variable {V W : Type*} [SetStructure V] [SetStructure W]

variable [Nonempty V] [Nonempty W] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [W↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem map_numeral (j : ElementaryMap V W) (n : ℕ) : j (n : V) = (n : W) := by
  exact (j.map_defined (numeralFormula n) (fun v ↦ v 0 = (n : V))
    (fun v ↦ v 0 = (n : W)) ![(n : V)]).mp rfl

theorem map_empty (j : ElementaryMap V W) : j (∅ : V) = (∅ : W) := by
  exact j.map_numeral 0

theorem map_assignmentPrepend (j : ElementaryMap V W) (n b x : V) :
    j (assignmentPrepend n b x) = assignmentPrepend (j n) (j b) (j x) := by
  exact (j.map_defined assignmentPrependFormula
    (fun v ↦ v 0 = assignmentPrepend (v 1) (v 2) (v 3))
    (fun v ↦ v 0 = assignmentPrepend (v 1) (v 2) (v 3))
    ![assignmentPrepend n b x, n, b, x]).mp rfl

theorem map_standardTuple (j : ElementaryMap V W) {n : ℕ} (v : Fin n → V) :
    j (standardTuple v) = standardTuple (j ∘ v) := by
  induction n with
  | zero => exact j.map_empty
  | succ n ih =>
    simp only [standardTuple, map_assignmentPrepend, map_numeral, ih, Function.comp_def]

end ElementaryMap
end ZFVP


