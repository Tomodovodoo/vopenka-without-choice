import ZFVP.Syntax.PrimitiveProgramListFold
import ZFVP.Syntax.PrimitiveProgramListExt

/-! Length and indexed-value equations for maps and concatenation on every internal list code. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.Arithmetic

namespace PrimitiveProgram

variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

@[simp] theorem evalArithmetic_listMap_length (f : PrimitiveProgram) (z xs : M) :
    listLength.evalArithmetic ((listMap f).evalArithmetic (Arithmetic.pair z xs)) = listLength.evalArithmetic xs := by
  induction xs using ISigma1.sigma1_order_induction
  · definability
  case ind xs ih =>
    rcases listCode_cases xs with rfl | ⟨x, tail, rfl⟩
    · simp
    · simp [ih tail (lt_succ_iff_le.mpr (le_pair_right x tail))]

theorem evalArithmetic_listMap_get (f : PrimitiveProgram) (z xs i : M)
    (hi : i < listLength.evalArithmetic xs) :
    listGet.evalArithmetic (Arithmetic.pair ((listMap f).evalArithmetic (Arithmetic.pair z xs)) i) =
      f.evalArithmetic (Arithmetic.pair z (listGet.evalArithmetic (Arithmetic.pair xs i))) := by
  induction xs using ISigma1.pi1_order_induction generalizing i
  · definability
  case ind xs ih =>
    rcases listCode_cases xs with rfl | ⟨x, tail, rfl⟩
    · simp at hi
    · rw [evalArithmetic_listMap_cons]
      rcases zero_or_succ i with rfl | ⟨i, rfl⟩
      · simp only [evalArithmetic_listGet_cons_zero]
      · simp only [evalArithmetic_listGet_cons_succ]
        exact ih tail (lt_succ_iff_le.mpr (le_pair_right x tail)) i (by simpa using hi)

@[simp] theorem evalArithmetic_listAppend_length (xs ys : M) :
    listLength.evalArithmetic (listAppend.evalArithmetic (Arithmetic.pair ys xs)) =
      listLength.evalArithmetic xs + listLength.evalArithmetic ys := by
  induction xs using ISigma1.sigma1_order_induction
  · definability
  case ind xs ih =>
    rcases listCode_cases xs with rfl | ⟨x, tail, rfl⟩
    · simp
    · simp only [evalArithmetic_listAppend_cons, evalArithmetic_listLength_cons,
        ih tail (lt_succ_iff_le.mpr (le_pair_right x tail))]
      ac_rfl

theorem evalArithmetic_listAppend_get_left (xs ys i : M) (hi : i < listLength.evalArithmetic xs) :
    listGet.evalArithmetic (Arithmetic.pair (listAppend.evalArithmetic (Arithmetic.pair ys xs)) i) =
      listGet.evalArithmetic (Arithmetic.pair xs i) := by
  induction xs using ISigma1.pi1_order_induction generalizing i
  · definability
  case ind xs ih =>
    rcases listCode_cases xs with rfl | ⟨x, tail, rfl⟩
    · simp at hi
    · rw [evalArithmetic_listAppend_cons]
      rcases zero_or_succ i with rfl | ⟨i, rfl⟩
      · simp only [evalArithmetic_listGet_cons_zero]
      · simp only [evalArithmetic_listGet_cons_succ]
        exact ih tail (lt_succ_iff_le.mpr (le_pair_right x tail)) i (by simpa using hi)

theorem evalArithmetic_listAppend_get_right (xs ys i : M) :
    listGet.evalArithmetic (Arithmetic.pair (listAppend.evalArithmetic (Arithmetic.pair ys xs))
      (listLength.evalArithmetic xs + i)) = listGet.evalArithmetic (Arithmetic.pair ys i) := by
  induction xs using ISigma1.sigma1_order_induction
  · definability
  case ind xs ih =>
    rcases listCode_cases xs with rfl | ⟨x, tail, rfl⟩
    · simp
    · rw [evalArithmetic_listAppend_cons, evalArithmetic_listLength_cons,
        show listLength.evalArithmetic tail + 1 + i = (listLength.evalArithmetic tail + i) + 1 by ac_rfl,
        evalArithmetic_listGet_cons_succ]
      exact ih tail (lt_succ_iff_le.mpr (le_pair_right x tail))

end PrimitiveProgram
end ZFVP
