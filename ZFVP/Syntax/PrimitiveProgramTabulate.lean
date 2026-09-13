import ZFVP.Syntax.PrimitiveProgramCourseRec

/-! Explicit finite tables of primitive-program values, stored in reverse index order. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.Arithmetic

namespace PrimitiveProgram

def tabulate (step : PrimitiveProgram) : PrimitiveProgram :=
  courseTable (.comp step (.pair .left (.comp .left .right)))

variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

@[simp] theorem evalArithmetic_tabulate_length (step : PrimitiveProgram) (z n : M) :
    listLength.evalArithmetic ((tabulate step).evalArithmetic (Arithmetic.pair z n)) = n := by
  simp [tabulate]

@[simp] theorem evalArithmetic_tabulate_zero (step : PrimitiveProgram) (z : M) :
    (tabulate step).evalArithmetic (Arithmetic.pair z 0) = 0 := by
  simp [tabulate]

theorem evalArithmetic_tabulate_succ (step : PrimitiveProgram) (z n : M) :
    (tabulate step).evalArithmetic (Arithmetic.pair z (n + 1)) =
      Arithmetic.pair (step.evalArithmetic (Arithmetic.pair z n))
        ((tabulate step).evalArithmetic (Arithmetic.pair z n)) + 1 := by
  simp [tabulate, evalArithmetic_courseTable_succ]

theorem evalArithmetic_tabulate_get (step : PrimitiveProgram) (z n i : M) (hi : i < n) :
    listGet.evalArithmetic (Arithmetic.pair ((tabulate step).evalArithmetic (Arithmetic.pair z n))
      (n - (i + 1))) = step.evalArithmetic (Arithmetic.pair z i) := by
  rw [tabulate, evalArithmetic_courseTable_get _ z n i hi, evalArithmetic_courseEval]
  simp

end PrimitiveProgram
end ZFVP