import ZFVP.Syntax.PrimitiveProgramFormulaRequirements
import ZFVP.Syntax.PrimitiveProgramListFold

/-! Explicit Boolean checks for formulas and lists of formulas in a fixed source context. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.Arithmetic

namespace PrimitiveProgram

def listAll (test : PrimitiveProgram) : PrimitiveProgram :=
  .comp (boundedAll (.comp test (.pair (.comp .left .left)
    (.comp listGet (.pair (.comp .right .left) .right)))))
    (.pair identity (.comp listLength .right))

def requirementCheck : PrimitiveProgram :=
  ifZero .right .zero (.comp lessEqual (.pair .right (.comp .succ .left)))

def formulaCheck (allowFree : Bool) : PrimitiveProgram :=
  .comp requirementCheck (.pair .left (.comp (formulaRequirement allowFree) .right))

def sequentCheck (allowFree : Bool) : PrimitiveProgram := listAll (formulaCheck allowFree)

variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

@[simp] theorem evalArithmetic_listAll_eq_one (test : PrimitiveProgram) (z xs : M) :
    (listAll test).evalArithmetic (Arithmetic.pair z xs) = 1 ↔
      ∀ i < listLength.evalArithmetic xs,
        test.evalArithmetic (Arithmetic.pair z (listGet.evalArithmetic (Arithmetic.pair xs i))) ≠ 0 := by
  simp [listAll]

@[simp] theorem evalArithmetic_requirementCheck_eq_one (n r : M) :
    requirementCheck.evalArithmetic (Arithmetic.pair n r) = 1 ↔ r ≠ 0 ∧ r ≤ n + 1 := by
  by_cases h : r = 0 <;> simp [requirementCheck, h]

@[simp] theorem evalArithmetic_requirementCheck_ne_zero (n r : M) :
    requirementCheck.evalArithmetic (Arithmetic.pair n r) ≠ 0 ↔ r ≠ 0 ∧ r ≤ n + 1 := by
  by_cases h : r = 0 <;> simp [requirementCheck, h]

@[simp] theorem evalArithmetic_formulaCheck_eq_one (allowFree : Bool) (n c : M) :
    (formulaCheck allowFree).evalArithmetic (Arithmetic.pair n c) = 1 ↔
      (formulaRequirement allowFree).evalArithmetic c ≠ 0 ∧
        (formulaRequirement allowFree).evalArithmetic c ≤ n + 1 := by
  simp [formulaCheck]

@[simp] theorem evalArithmetic_formulaCheck_ne_zero (allowFree : Bool) (n c : M) :
    (formulaCheck allowFree).evalArithmetic (Arithmetic.pair n c) ≠ 0 ↔
      (formulaRequirement allowFree).evalArithmetic c ≠ 0 ∧
        (formulaRequirement allowFree).evalArithmetic c ≤ n + 1 := by
  simp [formulaCheck]

@[simp] theorem evalArithmetic_sequentCheck_eq_one (allowFree : Bool) (n xs : M) :
    (sequentCheck allowFree).evalArithmetic (Arithmetic.pair n xs) = 1 ↔
      ∀ i < listLength.evalArithmetic xs,
        (formulaRequirement allowFree).evalArithmetic (listGet.evalArithmetic (Arithmetic.pair xs i)) ≠ 0 ∧
          (formulaRequirement allowFree).evalArithmetic (listGet.evalArithmetic (Arithmetic.pair xs i)) ≤ n + 1 := by
  simp [sequentCheck]

end PrimitiveProgram
end ZFVP
