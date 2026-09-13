import ZFVP.Syntax.PrimitiveProgramReindex

/-! Binder-lifting equations and bounds for arbitrary internal renaming tables. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.Arithmetic

namespace PrimitiveProgram

variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem arithmeticReindexVariable_below (r : M) {d i : M} (hi : i < d) :
    arithmeticReindexVariable r d i = i := by
  simp only [arithmeticReindexVariable, hi, ite_true]

theorem arithmeticReindexVariable_zeroDepth (r i : M) (hi : i < listLength.evalArithmetic r) :
    arithmeticReindexVariable r 0 i = listGet.evalArithmetic (Arithmetic.pair r i) := by
  simp [arithmeticReindexVariable, hi]

@[simp] theorem arithmeticReindexVariable_lift_zero (r d : M) :
    arithmeticReindexVariable r (d + 1) 0 = 0 := by
  apply arithmeticReindexVariable_below
  simp

theorem arithmeticReindexVariable_lift_succ (r d i : M) :
    arithmeticReindexVariable r (d + 1) (i + 1) = arithmeticReindexVariable r d i + 1 := by
  unfold arithmeticReindexVariable
  simp only [add_lt_add_iff_right, add_tsub_add_eq_tsub_right]
  split <;> simp [add_assoc]

theorem arithmeticReindexVariable_bound {r m d i : M}
    (hr : ∀ j < listLength.evalArithmetic r, listGet.evalArithmetic (Arithmetic.pair r j) < m)
    (hi : i < listLength.evalArithmetic r + d) : arithmeticReindexVariable r d i < m + d := by
  by_cases hid : i < d
  · rw [arithmeticReindexVariable_below r hid]
    exact lt_of_lt_of_le hid le_add_self
  · have hdi : d ≤ i := le_of_not_gt hid
    have hj : i - d < listLength.evalArithmetic r := by
      apply (add_lt_add_iff_right d).mp
      rwa [sub_add_self_of_le hdi]
    simp only [arithmeticReindexVariable, hid, ite_false, hj, ite_true]
    simpa only [add_comm] using add_lt_add_right (hr _ hj) d

theorem evalArithmetic_reindexTerm_bound (r d i : M) :
    reindexTerm.evalArithmetic (Arithmetic.pair r (Arithmetic.pair d (Arithmetic.pair 0 i + 1))) =
      Arithmetic.pair 0 (arithmeticReindexVariable r d i) + 1 := by
  simp [arithmeticReindexTerm]

end PrimitiveProgram
end ZFVP
