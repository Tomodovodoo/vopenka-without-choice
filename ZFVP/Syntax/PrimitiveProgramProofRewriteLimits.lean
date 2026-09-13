import ZFVP.Syntax.PrimitiveProgramProofRewrite
import ZFVP.Syntax.PrimitiveProgramFormulaTransformLimits

/-! Table-limit independence for the proof-rule rewrite specialization. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.Arithmetic

namespace PrimitiveProgram

variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem proofRewriteBounded_limit_independent (n s d D E : M)
    (hD : d + n ≤ D) (hE : d + n ≤ E) :
    proofRewriteBounded.evalArithmetic (Arithmetic.pair (Arithmetic.pair s D) (Arithmetic.pair n d)) =
      proofRewriteBounded.evalArithmetic (Arithmetic.pair (Arithmetic.pair s E) (Arithmetic.pair n d)) := by
  exact formulaTransformBounded_limit_independent proofRewriteArguments n s d D E hD hE

theorem evalArithmetic_proofRewriteBounded_eq_code (s D n d : M) (hD : d + n ≤ D) :
    proofRewriteBounded.evalArithmetic (Arithmetic.pair (Arithmetic.pair s D) (Arithmetic.pair n d)) =
      proofRewriteCode.evalArithmetic (Arithmetic.pair s (Arithmetic.pair d n)) := by
  exact evalArithmetic_formulaTransformBounded_eq_code proofRewriteArguments s D n d hD

end PrimitiveProgram
end ZFVP
