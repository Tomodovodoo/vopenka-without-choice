import ZFVP.Syntax.PrimitiveProgramNegation

/-! Repeated universal quantification through an arbitrary internal natural length. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.Arithmetic

namespace PrimitiveProgram

def universalClosure : PrimitiveProgram :=
  .comp (.prec identity (tagged 6 (.comp .right .right))) (.pair .right .left)

variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

@[simp] theorem evalArithmetic_universalClosure_zero (c : M) :
    universalClosure.evalArithmetic (Arithmetic.pair 0 c) = c := by
  simp [universalClosure]

@[simp] theorem evalArithmetic_universalClosure_succ (k c : M) :
    universalClosure.evalArithmetic (Arithmetic.pair (k + 1) c) =
      Arithmetic.pair 6 (universalClosure.evalArithmetic (Arithmetic.pair k c)) + 1 := by
  simp [universalClosure, evalArithmetic_prec_succ]

end PrimitiveProgram
end ZFVP
