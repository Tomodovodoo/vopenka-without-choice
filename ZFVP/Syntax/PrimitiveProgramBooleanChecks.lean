import ZFVP.Syntax.PrimitiveProgramSyntaxChecks
import ZFVP.Syntax.PrimitiveProgramListMembership

/-! Finite conjunction and Boolean normalization for explicit proof-checker tests. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.Arithmetic

namespace PrimitiveProgram

def allOf : List PrimitiveProgram → PrimitiveProgram
  | [] => constant 1
  | p :: ps => ifZero p .zero (allOf ps)

variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

@[simp] theorem evalArithmetic_allOf_eq_one (ps : List PrimitiveProgram) (x : M) :
    (allOf ps).evalArithmetic x = 1 ↔ ∀ p ∈ ps, p.evalArithmetic x ≠ 0 := by
  induction ps with
  | nil => simp [allOf]
  | cons p ps ih => by_cases hp : p.evalArithmetic x = 0 <;> simp [allOf, hp, ih]

@[simp] theorem evalArithmetic_allOf_ne_zero (ps : List PrimitiveProgram) (x : M) :
    (allOf ps).evalArithmetic x ≠ 0 ↔ ∀ p ∈ ps, p.evalArithmetic x ≠ 0 := by
  induction ps with
  | nil => simp [allOf]
  | cons p ps ih => by_cases hp : p.evalArithmetic x = 0 <;> simp [allOf, hp, ih]

@[simp] theorem evalArithmetic_listAll_ne_zero (test : PrimitiveProgram) (z xs : M) :
    (listAll test).evalArithmetic (Arithmetic.pair z xs) ≠ 0 ↔
      ∀ i < listLength.evalArithmetic xs,
        test.evalArithmetic (Arithmetic.pair z (listGet.evalArithmetic (Arithmetic.pair xs i))) ≠ 0 := by
  classical
  simp [listAll, evalArithmetic_boundedAll]

@[simp] theorem evalArithmetic_sequentCheck_ne_zero (allowFree : Bool) (n xs : M) :
    (sequentCheck allowFree).evalArithmetic (Arithmetic.pair n xs) ≠ 0 ↔
      ∀ i < listLength.evalArithmetic xs,
        (formulaRequirement allowFree).evalArithmetic (listGet.evalArithmetic (Arithmetic.pair xs i)) ≠ 0 ∧
          (formulaRequirement allowFree).evalArithmetic (listGet.evalArithmetic (Arithmetic.pair xs i)) ≤ n + 1 := by
  simp [sequentCheck]

@[simp] theorem evalArithmetic_listSubset_ne_zero (xs ys : M) :
    listSubset.evalArithmetic (Arithmetic.pair xs ys) ≠ 0 ↔
      ∀ i < listLength.evalArithmetic xs, ∃ j < listLength.evalArithmetic ys,
        listGet.evalArithmetic (Arithmetic.pair xs i) = listGet.evalArithmetic (Arithmetic.pair ys j) := by
  classical
  simp [listSubset, listSubsetTest, evalArithmetic_boundedAll]

end PrimitiveProgram
end ZFVP
