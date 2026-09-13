import ZFVP.Syntax.PrimitiveProgramProofRewriteVariables

/-! The concrete shift, eigenvariable, and witness modes on all internal indices. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.Arithmetic

namespace PrimitiveProgram

variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

@[simp] theorem evalArithmetic_proofRewriteFreshIndex_one :
    proofRewriteFreshIndex.evalArithmetic (1 : M) = 0 := by simp

@[simp] theorem evalArithmetic_proofRewriteFreshIndex_witness (k : M) :
    proofRewriteFreshIndex.evalArithmetic (k + 1 + 1) = k := by
  have hn : k + 2 ≠ 1 := ne_of_gt (one_lt_iff_two_le.mpr (by simp))
  simp [add_assoc, one_add_one_eq_two, hn]

@[simp] theorem evalArithmetic_proofRewriteFreeIndex_zero (i : M) :
    proofRewriteFreeIndex.evalArithmetic (Arithmetic.pair 0 i) = i + 1 := by simp

@[simp] theorem evalArithmetic_proofRewriteFreeIndex_one (i : M) :
    proofRewriteFreeIndex.evalArithmetic (Arithmetic.pair 1 i) = i + 1 := by simp

@[simp] theorem evalArithmetic_proofRewriteFreeIndex_witness (k i : M) :
    proofRewriteFreeIndex.evalArithmetic (Arithmetic.pair (k + 1 + 1) i) = i := by
  simp [add_assoc, one_add_one_eq_two]

end PrimitiveProgram
end ZFVP
