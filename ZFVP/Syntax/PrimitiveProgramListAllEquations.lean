import ZFVP.Syntax.PrimitiveProgramListMemberEquations
import ZFVP.Syntax.PrimitiveProgramBooleanChecks

/-! Constructor and concatenation equations for all-element and sequent syntax checks. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.Arithmetic

namespace PrimitiveProgram

variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem evalArithmetic_listAll_mem_iff (test : PrimitiveProgram) (z xs : M) :
    (listAll test).evalArithmetic (Arithmetic.pair z xs) = 1 ↔
      ∀ x, listMember.evalArithmetic (Arithmetic.pair x xs) = 1 → test.evalArithmetic (Arithmetic.pair z x) ≠ 0 := by
  rw [evalArithmetic_listAll_eq_one]
  constructor
  · intro h x hx
    obtain ⟨i, hi, he⟩ := (evalArithmetic_listMember_eq_one x xs).mp hx
    rw [he]
    exact h i hi
  · intro h i hi
    exact h _ ((evalArithmetic_listMember_eq_one _ xs).mpr ⟨i, hi, rfl⟩)

theorem evalArithmetic_listAll_cons_iff (test : PrimitiveProgram) (z x xs : M) :
    (listAll test).evalArithmetic (Arithmetic.pair z (Arithmetic.pair x xs + 1)) = 1 ↔
      test.evalArithmetic (Arithmetic.pair z x) ≠ 0 ∧ (listAll test).evalArithmetic (Arithmetic.pair z xs) = 1 := by
  simp only [evalArithmetic_listAll_mem_iff, evalArithmetic_listMember_cons_iff]
  constructor
  · intro h
    exact ⟨h x (Or.inl rfl), fun y hy ↦ h y (Or.inr hy)⟩
  · rintro ⟨hx, hxs⟩ y (he | hy)
    · exact he ▸ hx
    · exact hxs y hy

theorem evalArithmetic_listAll_append_iff (test : PrimitiveProgram) (z xs ys : M) :
    (listAll test).evalArithmetic (Arithmetic.pair z (listAppend.evalArithmetic (Arithmetic.pair ys xs))) = 1 ↔
      (listAll test).evalArithmetic (Arithmetic.pair z xs) = 1 ∧
        (listAll test).evalArithmetic (Arithmetic.pair z ys) = 1 := by
  simp only [evalArithmetic_listAll_mem_iff, evalArithmetic_listMember_append_iff]
  constructor
  · intro h
    exact ⟨fun x hx ↦ h x (Or.inl hx), fun x hx ↦ h x (Or.inr hx)⟩
  · rintro ⟨hxs, hys⟩ x (hx | hx)
    · exact hxs x hx
    · exact hys x hx

theorem evalArithmetic_sequentCheck_cons_iff (allowFree : Bool) (n x xs : M) :
    (sequentCheck allowFree).evalArithmetic (Arithmetic.pair n (Arithmetic.pair x xs + 1)) = 1 ↔
      (formulaCheck allowFree).evalArithmetic (Arithmetic.pair n x) = 1 ∧
        (sequentCheck allowFree).evalArithmetic (Arithmetic.pair n xs) = 1 := by
  change (listAll (formulaCheck allowFree)).evalArithmetic _ = 1 ↔ _
  rw [evalArithmetic_listAll_cons_iff]
  simp only [evalArithmetic_formulaCheck_ne_zero, evalArithmetic_formulaCheck_eq_one]
  rfl

theorem evalArithmetic_sequentCheck_append_iff (allowFree : Bool) (n xs ys : M) :
    (sequentCheck allowFree).evalArithmetic (Arithmetic.pair n (listAppend.evalArithmetic (Arithmetic.pair ys xs))) = 1 ↔
      (sequentCheck allowFree).evalArithmetic (Arithmetic.pair n xs) = 1 ∧
        (sequentCheck allowFree).evalArithmetic (Arithmetic.pair n ys) = 1 :=
  evalArithmetic_listAll_append_iff (formulaCheck allowFree) n xs ys

theorem evalArithmetic_listSubset_mem_iff (xs ys : M) :
    listSubset.evalArithmetic (Arithmetic.pair xs ys) = 1 ↔
      ∀ x, listMember.evalArithmetic (Arithmetic.pair x xs) = 1 → listMember.evalArithmetic (Arithmetic.pair x ys) = 1 := by
  simp only [evalArithmetic_listSubset_eq_one, evalArithmetic_listMember_eq_one]
  constructor
  · intro h x hx
    obtain ⟨i, hi, he⟩ := hx
    rw [he]
    exact h i hi
  · intro h i hi
    exact h _ ⟨i, hi, rfl⟩

end PrimitiveProgram
end ZFVP
