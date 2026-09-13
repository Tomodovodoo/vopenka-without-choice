import ZFVP.Syntax.PrimitiveProgramIndexedCourse
import ZFVP.Syntax.PrimitiveProgramProofRewriteTerm

/-! Formula transformation with a supplied argument program and finite tables for binder depth. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.Arithmetic

namespace PrimitiveProgram

def formulaTransformCell (arguments : PrimitiveProgram) : PrimitiveProgram :=
  let outer := .left
  let z := .comp .left outer
  let s := .comp .left z
  let D := .comp .right z
  let n := .comp .left (.comp .right outer)
  let table := .comp .right (.comp .right outer)
  let d := .right
  let t := .comp listHead n
  let c := .comp listTail n
  let previous := fun child depth ↦ .comp listGet (.pair
    (.comp listGet (.pair table (.comp subtraction (.pair n (.comp .succ child)))))
    (.comp subtraction (.pair D depth)))
  let args := .comp arguments (.pair s (.pair d (.comp .right (.comp .right c))))
  let atom := .pair (constant 2) (.pair (.comp .left (.comp .right c)) args)
  let bin := .pair (previous (.comp .left c) d) (previous (.comp .right c) d)
  let quant := previous c (.comp .succ d)
  ifZero n .zero
    (ifEqual t (constant 0) (tagged 0 atom)
    (ifEqual t (constant 1) (tagged 1 atom)
    (ifEqual t (constant 2) (tagged 2 .zero)
    (ifEqual t (constant 3) (tagged 3 .zero)
    (ifEqual t (constant 4) (tagged 4 bin)
    (ifEqual t (constant 5) (tagged 5 bin)
    (ifEqual t (constant 6) (tagged 6 quant)
    (ifEqual t (constant 7) (tagged 7 quant) .zero))))))))

def formulaTransformBounded (arguments : PrimitiveProgram) : PrimitiveProgram := indexedCourseEval (formulaTransformCell arguments)

/-- Input is `(parameter, (initialDepth, formulaCode))`; the argument program receives the same parameter and depth. -/
def formulaTransformCode (arguments : PrimitiveProgram) : PrimitiveProgram :=
  .comp (formulaTransformBounded arguments) (.pair
    (.pair .left (.comp addition (.pair (.comp .left .right) (.comp .right .right))))
    (.pair (.comp .right .right) (.comp .left .right)))

variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

noncomputable def arithmeticFormulaTransformValue (arguments : PrimitiveProgram) (s d t c : M) (F : M → M → M) : M :=
  let atom := Arithmetic.pair 2 (Arithmetic.pair (Arithmetic.pi₁ (Arithmetic.pi₂ c))
    (arguments.evalArithmetic (Arithmetic.pair s (Arithmetic.pair d (Arithmetic.pi₂ (Arithmetic.pi₂ c))))))
  let bin := Arithmetic.pair (F (Arithmetic.pi₁ c) d) (F (Arithmetic.pi₂ c) d)
  let quant := F c (d + 1)
  if t = 0 then Arithmetic.pair 0 atom + 1
  else if t = 1 then Arithmetic.pair 1 atom + 1
  else if t = 2 then Arithmetic.pair 2 0 + 1
  else if t = 3 then Arithmetic.pair 3 0 + 1
  else if t = 4 then Arithmetic.pair 4 bin + 1
  else if t = 5 then Arithmetic.pair 5 bin + 1
  else if t = 6 then Arithmetic.pair 6 quant + 1
  else if t = 7 then Arithmetic.pair 7 quant + 1
  else 0

@[simp] theorem evalArithmetic_formulaTransformCell (arguments : PrimitiveProgram) (s D n table d : M) :
    (formulaTransformCell arguments).evalArithmetic (Arithmetic.pair
      (Arithmetic.pair (Arithmetic.pair s D) (Arithmetic.pair n table)) d) =
      if n = 0 then 0 else (arithmeticFormulaTransformValue arguments) s d (Arithmetic.pi₁ (n - 1)) (Arithmetic.pi₂ (n - 1))
        (fun child depth ↦ listGet.evalArithmetic (Arithmetic.pair
          (listGet.evalArithmetic (Arithmetic.pair table (n - (child + 1)))) (D - depth))) := by
  simp [formulaTransformCell, arithmeticFormulaTransformValue]

theorem evalArithmetic_formulaTransformBounded (arguments : PrimitiveProgram) (s D n d : M) (hd : d ≤ D) :
    (formulaTransformBounded arguments).evalArithmetic (Arithmetic.pair (Arithmetic.pair s D) (Arithmetic.pair n d)) =
      if n = 0 then 0 else (arithmeticFormulaTransformValue arguments) s d (Arithmetic.pi₁ (n - 1)) (Arithmetic.pi₂ (n - 1))
        (fun child depth ↦ listGet.evalArithmetic (Arithmetic.pair
          (listGet.evalArithmetic (Arithmetic.pair
            ((courseTable (indexedCourseStep (formulaTransformCell arguments))).evalArithmetic (Arithmetic.pair (Arithmetic.pair s D) n))
            (n - (child + 1)))) (D - depth))) := by
  rw [formulaTransformBounded, evalArithmetic_indexedCourseEval _ s D n d hd, (evalArithmetic_formulaTransformCell arguments)]

@[simp] theorem evalArithmetic_formulaTransformCode (arguments : PrimitiveProgram) (s d n : M) :
    (formulaTransformCode arguments).evalArithmetic (Arithmetic.pair s (Arithmetic.pair d n)) =
      (formulaTransformBounded arguments).evalArithmetic (Arithmetic.pair (Arithmetic.pair s (d + n)) (Arithmetic.pair n d)) := by
  simp [formulaTransformCode]

theorem evalArithmetic_formulaTransformBounded_tagged (arguments : PrimitiveProgram) (s D t c d : M) (hd : d ≤ D) :
    (formulaTransformBounded arguments).evalArithmetic (Arithmetic.pair (Arithmetic.pair s D) (Arithmetic.pair (Arithmetic.pair t c + 1) d)) =
      (arithmeticFormulaTransformValue arguments) s d t c
        (fun child depth ↦ (formulaTransformBounded arguments).evalArithmetic (Arithmetic.pair (Arithmetic.pair s D) (Arithmetic.pair child depth))) := by
  have hc : c < Arithmetic.pair t c + 1 := lt_succ_iff_le.mpr (le_pair_right t c)
  have hl : Arithmetic.pi₁ c < Arithmetic.pair t c + 1 := lt_of_le_of_lt (pi₁_le_self c) hc
  have hr : Arithmetic.pi₂ c < Arithmetic.pair t c + 1 := lt_of_le_of_lt (pi₂_le_self c) hc
  rw [(evalArithmetic_formulaTransformBounded arguments) s D _ d hd]
  simp only [show Arithmetic.pair t c + 1 ≠ (0 : M) from by simp, ite_false,
    Arithmetic.add_sub_self, Arithmetic.pi₁_pair, Arithmetic.pi₂_pair,
    arithmeticFormulaTransformValue, evalArithmetic_indexedCourse_previous _ s D _ (d + 1) c hc,
    evalArithmetic_indexedCourse_previous _ s D _ d (Arithmetic.pi₁ c) hl,
    evalArithmetic_indexedCourse_previous _ s D _ d (Arithmetic.pi₂ c) hr, formulaTransformBounded]

end PrimitiveProgram
end ZFVP