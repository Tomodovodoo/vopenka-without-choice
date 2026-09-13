import ZFVP.Syntax.PrimitiveProgramFormulaRequirements
import ZFVP.Syntax.PrimitiveProgramListExt

/-! Exact semantic characterizations of the atomic syntax requirement programs. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.Arithmetic

namespace PrimitiveProgram

variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem termRequirement_valid_iff (allowFree : Bool) (c n : M) :
    ((termRequirement allowFree).evalArithmetic c ≠ 0 ∧
      (termRequirement allowFree).evalArithmetic c ≤ n + 1) ↔
      (∃ i < n, c = Arithmetic.pair 0 i + 1) ∨
      (allowFree = true ∧ ∃ i, c = Arithmetic.pair 1 i + 1) := by
  rcases listCode_cases c with (rfl | ⟨t, i, rfl⟩)
  · simp
  by_cases ht : t = 0
  · subst t
    simp [succ_le_iff_lt]
  by_cases ht1 : t = 1
  · subst t
    cases allowFree <;> simp
  · simp [ht, ht1]

theorem atomicRequirement_valid_iff (allowFree : Bool) (k r args n : M) :
    ((atomicRequirement allowFree).evalArithmetic (Arithmetic.pair k (Arithmetic.pair r args)) ≠ 0 ∧
      (atomicRequirement allowFree).evalArithmetic (Arithmetic.pair k (Arithmetic.pair r args)) ≤ n + 1) ↔
      k = 2 ∧ r ≤ 1 ∧ listLength.evalArithmetic args = 2 ∧
        ((termRequirement allowFree).evalArithmetic (listHead.evalArithmetic args) ≠ 0 ∧
          (termRequirement allowFree).evalArithmetic (listHead.evalArithmetic args) ≤ n + 1) ∧
        ((termRequirement allowFree).evalArithmetic (listHead.evalArithmetic (listTail.evalArithmetic args)) ≠ 0 ∧
          (termRequirement allowFree).evalArithmetic (listHead.evalArithmetic (listTail.evalArithmetic args)) ≤ n + 1) := by
  rw [evalArithmetic_atomicRequirement]
  by_cases hk : k = 2
  · by_cases hr : r ≤ 1
    · by_cases hl : listLength.evalArithmetic args = 2
      · simp only [hk, hr, hl, ite_true, true_and]
        exact joinRequirements_valid_iff _ _ _
      · simp [hl]
    · simp [hr]
  · simp [hk]

end PrimitiveProgram
end ZFVP