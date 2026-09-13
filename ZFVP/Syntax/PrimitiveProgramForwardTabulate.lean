import ZFVP.Syntax.PrimitiveProgramListMap

/-! An explicit table of the values f(z,0),...,f(z,n-1), in increasing index order. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.Arithmetic

namespace PrimitiveProgram

def forwardTabulate (f : PrimitiveProgram) : PrimitiveProgram :=
  .prec .zero (.comp listAppend (.pair
    (.comp .succ (.pair (.comp f (.pair .left (.comp .left .right))) .zero))
    (.comp .right .right)))

variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

@[simp] theorem evalArithmetic_forwardTabulate_zero (f : PrimitiveProgram) (z : M) :
    (forwardTabulate f).evalArithmetic (Arithmetic.pair z 0) = 0 := by
  simp [forwardTabulate]

@[simp] theorem evalArithmetic_forwardTabulate_succ (f : PrimitiveProgram) (z n : M) :
    (forwardTabulate f).evalArithmetic (Arithmetic.pair z (n + 1)) =
      listAppend.evalArithmetic (Arithmetic.pair
        (Arithmetic.pair (f.evalArithmetic (Arithmetic.pair z n)) 0 + 1)
        ((forwardTabulate f).evalArithmetic (Arithmetic.pair z n))) := by
  simp [forwardTabulate, evalArithmetic_prec_succ]

@[simp] theorem evalArithmetic_forwardTabulate_length (f : PrimitiveProgram) (z n : M) :
    listLength.evalArithmetic ((forwardTabulate f).evalArithmetic (Arithmetic.pair z n)) = n := by
  induction n using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp
  case succ n ih => simp [ih]

theorem evalArithmetic_forwardTabulate_get (f : PrimitiveProgram) (z n i : M) (hi : i < n) :
    listGet.evalArithmetic (Arithmetic.pair ((forwardTabulate f).evalArithmetic (Arithmetic.pair z n)) i) =
      f.evalArithmetic (Arithmetic.pair z i) := by
  induction n using ISigma1.pi1_succ_induction generalizing i
  · definability
  case zero => exact False.elim (not_lt_zero hi)
  case succ n ih =>
    rw [evalArithmetic_forwardTabulate_succ]
    rcases lt_or_eq_of_le (lt_succ_iff_le.mp hi) with hi | he
    · rw [evalArithmetic_listAppend_get_left _ _ _ (by simpa using hi)]
      exact ih i hi
    · subst i
      have hn := evalArithmetic_forwardTabulate_length f z n
      have h := evalArithmetic_listAppend_get_right
        ((forwardTabulate f).evalArithmetic (Arithmetic.pair z n))
        (Arithmetic.pair (f.evalArithmetic (Arithmetic.pair z n)) 0 + 1) 0
      simpa only [hn, add_zero, evalArithmetic_listGet_cons_zero] using h

end PrimitiveProgram
end ZFVP
