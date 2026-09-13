import ZFVP.Syntax.PrimitiveProgramProofRewriteTerm

/-! Variable equations used to identify the internal eigenvariable and witness substitutions. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.Arithmetic

namespace PrimitiveProgram

def proofRewriteFreshIndex : PrimitiveProgram :=
  ifEqual identity (constant 1) .zero (.comp subtraction (.pair identity (constant 2)))

def proofRewriteFreeIndex : PrimitiveProgram :=
  ifLess .left (constant 2) (.comp .succ .right) .right

variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

@[simp] theorem evalArithmetic_proofRewriteFreshIndex (s : M) :
    proofRewriteFreshIndex.evalArithmetic s = if s = 1 then 0 else s - 2 := by
  simp [proofRewriteFreshIndex]

@[simp] theorem evalArithmetic_proofRewriteFreeIndex (s i : M) :
    proofRewriteFreeIndex.evalArithmetic (Arithmetic.pair s i) = if s < 2 then i + 1 else i := by
  simp [proofRewriteFreeIndex]

theorem evalArithmetic_proofRewriteTerm_bound_zeroMode (d i : M) :
    proofRewriteTerm.evalArithmetic (Arithmetic.pair 0 (Arithmetic.pair d (Arithmetic.pair 0 i + 1))) =
      Arithmetic.pair 0 i + 1 := by
  simp [arithmeticProofRewriteTerm]

theorem evalArithmetic_proofRewriteTerm_bound_below (s : M) {d i : M} (hi : i < d) :
    proofRewriteTerm.evalArithmetic (Arithmetic.pair s (Arithmetic.pair d (Arithmetic.pair 0 i + 1))) =
      Arithmetic.pair 0 i + 1 := by
  simp [arithmeticProofRewriteTerm, hi]

theorem evalArithmetic_proofRewriteTerm_bound_edge {s : M} (hs : s ≠ 0) (d : M) :
    proofRewriteTerm.evalArithmetic (Arithmetic.pair s (Arithmetic.pair d (Arithmetic.pair 0 d + 1))) =
      Arithmetic.pair 1 (if s = 1 then 0 else s - 2) + 1 := by
  simp [arithmeticProofRewriteTerm, hs]

theorem evalArithmetic_proofRewriteTerm_free (s d i : M) :
    proofRewriteTerm.evalArithmetic (Arithmetic.pair s (Arithmetic.pair d (Arithmetic.pair 1 i + 1))) =
      Arithmetic.pair 1 (if s < 2 then i + 1 else i) + 1 := by
  simp [arithmeticProofRewriteTerm]

end PrimitiveProgram
end ZFVP
