import ZFVP.Syntax.PrimitiveProgramListLength

/-! Explicit course-of-values recursion with a reversed table of prior results. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.Arithmetic

namespace PrimitiveProgram

def courseTable (step : PrimitiveProgram) : PrimitiveProgram :=
  .prec .zero (.comp .succ (.pair step (.comp .right .right)))

def courseEval (step : PrimitiveProgram) : PrimitiveProgram :=
  .comp listHead (.comp (courseTable step) (.pair .left (.comp .succ .right)))

variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

@[simp] theorem evalArithmetic_courseTable_zero (step : PrimitiveProgram) (z : M) :
    (courseTable step).evalArithmetic (Arithmetic.pair z 0) = 0 := by simp [courseTable]

theorem evalArithmetic_courseTable_succ (step : PrimitiveProgram) (z n : M) :
    (courseTable step).evalArithmetic (Arithmetic.pair z (n + 1)) =
      Arithmetic.pair (step.evalArithmetic (Arithmetic.pair z (Arithmetic.pair n
        ((courseTable step).evalArithmetic (Arithmetic.pair z n)))))
        ((courseTable step).evalArithmetic (Arithmetic.pair z n)) + 1 := by
  rw [courseTable, evalArithmetic_prec_succ]
  simp

theorem evalArithmetic_courseEval (step : PrimitiveProgram) (z n : M) :
    (courseEval step).evalArithmetic (Arithmetic.pair z n) =
      step.evalArithmetic (Arithmetic.pair z (Arithmetic.pair n
        ((courseTable step).evalArithmetic (Arithmetic.pair z n)))) := by
  simp [courseEval, evalArithmetic_courseTable_succ]

@[simp] theorem evalArithmetic_courseTable_length (step : PrimitiveProgram) (z n : M) :
    listLength.evalArithmetic ((courseTable step).evalArithmetic (Arithmetic.pair z n)) = n := by
  induction n using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp
  case succ n ih => simp [evalArithmetic_courseTable_succ, ih]

theorem evalArithmetic_courseTable_get (step : PrimitiveProgram) (z n i : M) (hi : i < n) :
    listGet.evalArithmetic (Arithmetic.pair ((courseTable step).evalArithmetic (Arithmetic.pair z n)) (n - (i + 1))) =
      (courseEval step).evalArithmetic (Arithmetic.pair z i) := by
  induction n using ISigma1.pi1_succ_induction generalizing i
  · definability
  case zero => simp at hi
  case succ n ih =>
    rcases (lt_succ_iff_le.mp hi).lt_or_eq with hin | rfl
    · have hidx : n + 1 - (i + 1) = (n - (i + 1)) + 1 := by
        simpa only [add_comm] using Arithmetic.add_sub_of_le (lt_iff_succ_le.mp hin) 1
      rw [hidx, evalArithmetic_courseTable_succ, evalArithmetic_listGet_cons_succ]
      exact ih i hin
    · simp [evalArithmetic_courseTable_succ, evalArithmetic_courseEval]

end PrimitiveProgram
end ZFVP
