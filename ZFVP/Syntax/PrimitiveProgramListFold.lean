import ZFVP.Syntax.PrimitiveProgramNegation

/-! Explicit right folds, maps and concatenation on internal natural-number list codes. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.Arithmetic

namespace PrimitiveProgram

def listFoldStep (initial step : PrimitiveProgram) : PrimitiveProgram :=
  let n := .comp .left .right
  let table := .comp .right .right
  let tail := .comp listTail n
  let previous := .comp listGet (.pair table (.comp subtraction (.pair n (.comp .succ tail))))
  ifZero n (.comp initial .left)
    (.comp step (.pair .left (.pair (.comp listHead n) previous)))

def listFold (initial step : PrimitiveProgram) : PrimitiveProgram := courseEval (listFoldStep initial step)

def listMap (f : PrimitiveProgram) : PrimitiveProgram :=
  listFold .zero (.comp .succ (.pair (.comp f (.pair .left (.comp .left .right))) (.comp .right .right)))

/-- Input is the pair of the right-hand list and the left-hand list. -/
def listAppend : PrimitiveProgram :=
  listFold identity (.comp .succ (.pair (.comp .left .right) (.comp .right .right)))

variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem evalArithmetic_listFoldStep (initial step : PrimitiveProgram) (z n table : M) :
    (listFoldStep initial step).evalArithmetic (Arithmetic.pair z (Arithmetic.pair n table)) =
      if n = 0 then initial.evalArithmetic z else
        step.evalArithmetic (Arithmetic.pair z (Arithmetic.pair (listHead.evalArithmetic n)
          (listGet.evalArithmetic (Arithmetic.pair table (n - (listTail.evalArithmetic n + 1)))))) := by
  simp [listFoldStep]

@[simp] theorem evalArithmetic_listFold_zero (initial step : PrimitiveProgram) (z : M) :
    (listFold initial step).evalArithmetic (Arithmetic.pair z 0) = initial.evalArithmetic z := by
  rw [listFold, evalArithmetic_courseEval]
  simp [listFoldStep]

@[simp] theorem evalArithmetic_listFold_cons (initial step : PrimitiveProgram) (z x xs : M) :
    (listFold initial step).evalArithmetic (Arithmetic.pair z (Arithmetic.pair x xs + 1)) =
      step.evalArithmetic (Arithmetic.pair z (Arithmetic.pair x
        ((listFold initial step).evalArithmetic (Arithmetic.pair z xs)))) := by
  rw [listFold, evalArithmetic_courseEval, evalArithmetic_listFoldStep]
  have hp := evalArithmetic_courseTable_get (listFoldStep initial step) z (Arithmetic.pair x xs + 1) xs
    (lt_succ_iff_le.mpr (le_pair_right x xs))
  have hn : Arithmetic.pair x xs + 1 ≠ 0 := by simp
  simp only [hn, ite_false, evalArithmetic_listHead_cons, evalArithmetic_listTail_cons, hp]

@[simp] theorem evalArithmetic_listMap_zero (f : PrimitiveProgram) (z : M) :
    (listMap f).evalArithmetic (Arithmetic.pair z 0) = 0 := by simp [listMap]

@[simp] theorem evalArithmetic_listMap_cons (f : PrimitiveProgram) (z x xs : M) :
    (listMap f).evalArithmetic (Arithmetic.pair z (Arithmetic.pair x xs + 1)) =
      Arithmetic.pair (f.evalArithmetic (Arithmetic.pair z x))
        ((listMap f).evalArithmetic (Arithmetic.pair z xs)) + 1 := by
  simp [listMap]

@[simp] theorem evalArithmetic_listAppend_zero (ys : M) :
    listAppend.evalArithmetic (Arithmetic.pair ys 0) = ys := by simp [listAppend]

@[simp] theorem evalArithmetic_listAppend_cons (ys x xs : M) :
    listAppend.evalArithmetic (Arithmetic.pair ys (Arithmetic.pair x xs + 1)) =
      Arithmetic.pair x (listAppend.evalArithmetic (Arithmetic.pair ys xs)) + 1 := by
  simp [listAppend]

end PrimitiveProgram
end ZFVP
