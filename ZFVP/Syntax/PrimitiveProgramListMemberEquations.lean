import ZFVP.Syntax.PrimitiveProgramListMap
import ZFVP.Syntax.PrimitiveProgramListMembership

/-! Exact list-membership equations for constructors, maps and concatenation. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.Arithmetic

namespace PrimitiveProgram

variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

@[simp] theorem evalArithmetic_listMember_zero_iff (x : M) :
    listMember.evalArithmetic (Arithmetic.pair x 0) = 1 ↔ False := by simp

theorem evalArithmetic_listMember_cons_iff (x y ys : M) :
    listMember.evalArithmetic (Arithmetic.pair x (Arithmetic.pair y ys + 1)) = 1 ↔
      x = y ∨ listMember.evalArithmetic (Arithmetic.pair x ys) = 1 := by
  simp only [evalArithmetic_listMember_eq_one, evalArithmetic_listLength_cons]
  constructor
  · rintro ⟨i, hi, he⟩
    rcases zero_or_succ i with rfl | ⟨i, rfl⟩
    · exact Or.inl (by simpa only [evalArithmetic_listGet_cons_zero] using he)
    · exact Or.inr ⟨i, by simpa using hi, by simpa only [evalArithmetic_listGet_cons_succ] using he⟩
  · rintro (he | ⟨i, hi, he⟩)
    · exact ⟨0, by simp, by simpa only [evalArithmetic_listGet_cons_zero] using he⟩
    · exact ⟨i + 1, by simpa using hi, by simpa only [evalArithmetic_listGet_cons_succ] using he⟩

theorem evalArithmetic_listMember_append_iff (x xs ys : M) :
    listMember.evalArithmetic (Arithmetic.pair x (listAppend.evalArithmetic (Arithmetic.pair ys xs))) = 1 ↔
      listMember.evalArithmetic (Arithmetic.pair x xs) = 1 ∨
        listMember.evalArithmetic (Arithmetic.pair x ys) = 1 := by
  induction xs using ISigma1.sigma1_order_induction
  · definability
  case ind xs ih =>
    rcases listCode_cases xs with rfl | ⟨y, tail, rfl⟩
    · simp
    · rw [evalArithmetic_listAppend_cons, evalArithmetic_listMember_cons_iff,
        ih tail (lt_succ_iff_le.mpr (le_pair_right y tail)), evalArithmetic_listMember_cons_iff]
      exact or_assoc.symm

theorem evalArithmetic_listMember_map_iff (f : PrimitiveProgram) (z x xs : M) :
    listMember.evalArithmetic (Arithmetic.pair x ((listMap f).evalArithmetic (Arithmetic.pair z xs))) = 1 ↔
      ∃ i < listLength.evalArithmetic xs,
        x = f.evalArithmetic (Arithmetic.pair z (listGet.evalArithmetic (Arithmetic.pair xs i))) := by
  rw [evalArithmetic_listMember_eq_one, evalArithmetic_listMap_length]
  exact exists_congr (fun i ↦ and_congr_right (fun hi ↦ by rw [evalArithmetic_listMap_get f z xs i hi]))

end PrimitiveProgram
end ZFVP
