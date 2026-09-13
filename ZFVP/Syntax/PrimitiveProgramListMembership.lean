import ZFVP.Syntax.PrimitiveProgramListLength

/-! Explicit membership and inclusion tests for internal natural-number list codes. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.Arithmetic

namespace PrimitiveProgram

def listMemberTest : PrimitiveProgram :=
  .comp equal (.pair (.comp .left .left) (.comp listGet (.pair (.comp .right .left) .right)))

def listMember : PrimitiveProgram :=
  .comp (boundedExists listMemberTest) (.pair identity (.comp listLength .right))

def listSubsetTest : PrimitiveProgram :=
  .comp listMember (.pair (.comp listGet (.pair (.comp .left .left) .right)) (.comp .right .left))

def listSubset : PrimitiveProgram :=
  .comp (boundedAll listSubsetTest) (.pair identity (.comp listLength .left))

variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

@[simp] theorem evalArithmetic_listMemberTest (x xs i : M) :
    listMemberTest.evalArithmetic (Arithmetic.pair (Arithmetic.pair x xs) i) =
      if x = listGet.evalArithmetic (Arithmetic.pair xs i) then 1 else 0 := by
  simp [listMemberTest]

@[simp] theorem evalArithmetic_listMember_eq_one (x xs : M) :
    listMember.evalArithmetic (Arithmetic.pair x xs) = 1 ↔
      ∃ i < listLength.evalArithmetic xs, x = listGet.evalArithmetic (Arithmetic.pair xs i) := by
  simp [listMember]

@[simp] theorem evalArithmetic_listMember_ne_zero (x xs : M) :
    listMember.evalArithmetic (Arithmetic.pair x xs) ≠ 0 ↔
      ∃ i < listLength.evalArithmetic xs, x = listGet.evalArithmetic (Arithmetic.pair xs i) := by
  classical
  simp [listMember, boundedExists, evalArithmetic_boundedAll, not_forall]

@[simp] theorem evalArithmetic_listSubset_eq_one (xs ys : M) :
    listSubset.evalArithmetic (Arithmetic.pair xs ys) = 1 ↔
      ∀ i < listLength.evalArithmetic xs, ∃ j < listLength.evalArithmetic ys,
        listGet.evalArithmetic (Arithmetic.pair xs i) = listGet.evalArithmetic (Arithmetic.pair ys j) := by
  simp [listSubset, listSubsetTest]

end PrimitiveProgram
end ZFVP
