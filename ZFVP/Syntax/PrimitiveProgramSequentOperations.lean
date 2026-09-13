import ZFVP.Syntax.PrimitiveProgramListMap
import ZFVP.Syntax.PrimitiveProgramProofRewriteEquations

/-! Explicit whole-sequent rewriting for the natural-number proof checker. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.Arithmetic

namespace PrimitiveProgram

def proofRewriteAtZero : PrimitiveProgram := .comp proofRewriteCode (.pair .left (.pair .zero .right))

def proofRewriteSequent : PrimitiveProgram := listMap proofRewriteAtZero

variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

@[simp] theorem evalArithmetic_proofRewriteAtZero (s c : M) :
    proofRewriteAtZero.evalArithmetic (Arithmetic.pair s c) =
      proofRewriteCode.evalArithmetic (Arithmetic.pair s (Arithmetic.pair 0 c)) := by
  simp only [proofRewriteAtZero, evalArithmetic_comp, evalArithmetic_pair, evalArithmetic_left,
    evalArithmetic_right, pi₁_pair, pi₂_pair, evalArithmetic_zero]

@[simp] theorem evalArithmetic_proofRewriteSequent_zero (s : M) :
    proofRewriteSequent.evalArithmetic (Arithmetic.pair s 0) = 0 := by simp [proofRewriteSequent]

@[simp] theorem evalArithmetic_proofRewriteSequent_cons (s c cs : M) :
    proofRewriteSequent.evalArithmetic (Arithmetic.pair s (Arithmetic.pair c cs + 1)) =
      Arithmetic.pair (proofRewriteCode.evalArithmetic (Arithmetic.pair s (Arithmetic.pair 0 c)))
        (proofRewriteSequent.evalArithmetic (Arithmetic.pair s cs)) + 1 := by
  simp only [proofRewriteSequent, evalArithmetic_listMap_cons, evalArithmetic_proofRewriteAtZero]

end PrimitiveProgram
end ZFVP
