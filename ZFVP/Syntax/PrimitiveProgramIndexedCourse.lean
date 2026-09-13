import ZFVP.Syntax.PrimitiveProgramTabulate

/-! Course-of-values tables with a bounded auxiliary index for each earlier result. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.Arithmetic

namespace PrimitiveProgram

/-- A cell step receives `((parameter, limit), (index, history)), auxiliaryIndex`. -/
def indexedCourseStep (step : PrimitiveProgram) : PrimitiveProgram :=
  .comp (tabulate step) (.pair identity (.comp .succ (.comp .right .left)))

/-- Input is `((parameter, limit), (index, auxiliaryIndex))`. -/
def indexedCourseEval (step : PrimitiveProgram) : PrimitiveProgram :=
  .comp listGet (.pair
    (.comp (courseEval (indexedCourseStep step)) (.pair .left (.comp .left .right)))
    (.comp subtraction (.pair (.comp .right .left) (.comp .right .right))))

variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

@[simp] theorem evalArithmetic_indexedCourseStep (step : PrimitiveProgram) (s D n table : M) :
    (indexedCourseStep step).evalArithmetic (Arithmetic.pair (Arithmetic.pair s D) (Arithmetic.pair n table)) =
      (tabulate step).evalArithmetic (Arithmetic.pair
        (Arithmetic.pair (Arithmetic.pair s D) (Arithmetic.pair n table)) (D + 1)) := by
  simp [indexedCourseStep]

theorem evalArithmetic_indexedCourseEval_unfold (step : PrimitiveProgram) (s D n d : M) :
    (indexedCourseEval step).evalArithmetic (Arithmetic.pair (Arithmetic.pair s D) (Arithmetic.pair n d)) =
      listGet.evalArithmetic (Arithmetic.pair
        ((courseEval (indexedCourseStep step)).evalArithmetic (Arithmetic.pair (Arithmetic.pair s D) n))
        (D - d)) := by
  simp [indexedCourseEval]

theorem evalArithmetic_indexedCourseEval (step : PrimitiveProgram) (s D n d : M) (hd : d ≤ D) :
    (indexedCourseEval step).evalArithmetic (Arithmetic.pair (Arithmetic.pair s D) (Arithmetic.pair n d)) =
      step.evalArithmetic (Arithmetic.pair
        (Arithmetic.pair (Arithmetic.pair s D) (Arithmetic.pair n
          ((courseTable (indexedCourseStep step)).evalArithmetic (Arithmetic.pair (Arithmetic.pair s D) n)))) d) := by
  rw [evalArithmetic_indexedCourseEval_unfold, evalArithmetic_courseEval, evalArithmetic_indexedCourseStep]
  have hi : (D + 1) - (d + 1) = D - d := add_tsub_add_eq_tsub_right D 1 d
  rw [← hi, evalArithmetic_tabulate_get _ _ _ _ (lt_succ_iff_le.mpr hd)]

theorem evalArithmetic_indexedCourse_previous (step : PrimitiveProgram) (s D n d i : M) (hi : i < n) :
    listGet.evalArithmetic (Arithmetic.pair
      (listGet.evalArithmetic (Arithmetic.pair
        ((courseTable (indexedCourseStep step)).evalArithmetic (Arithmetic.pair (Arithmetic.pair s D) n))
        (n - (i + 1)))) (D - d)) =
      (indexedCourseEval step).evalArithmetic (Arithmetic.pair (Arithmetic.pair s D) (Arithmetic.pair i d)) := by
  rw [evalArithmetic_courseTable_get _ _ n i hi, evalArithmetic_indexedCourseEval_unfold]

end PrimitiveProgram
end ZFVP