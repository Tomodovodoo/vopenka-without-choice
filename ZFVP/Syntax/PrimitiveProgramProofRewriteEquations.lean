import ZFVP.Syntax.PrimitiveProgramProofRewriteLimits
import ZFVP.Syntax.PrimitiveProgramFormulaTransformEquations

/-! Constructor equations for the proof-rule rewrite specialization. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.Arithmetic

namespace PrimitiveProgram

variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem evalArithmetic_proofRewriteCode_tagged (s d t c : M) :
    proofRewriteCode.evalArithmetic (Arithmetic.pair s (Arithmetic.pair d (Arithmetic.pair t c + 1))) =
      arithmeticProofRewriteValue s d t c
        (fun child depth ↦ proofRewriteCode.evalArithmetic (Arithmetic.pair s (Arithmetic.pair depth child))) := by
  exact evalArithmetic_formulaTransformCode_tagged proofRewriteArguments s d t c

@[simp] theorem evalArithmetic_proofRewriteCode_zero (s d : M) :
    proofRewriteCode.evalArithmetic (Arithmetic.pair s (Arithmetic.pair d 0)) = 0 := by
  exact evalArithmetic_formulaTransformCode_zero proofRewriteArguments s d

@[simp] theorem evalArithmetic_proofRewriteCode_rel (s d c : M) :
    proofRewriteCode.evalArithmetic (Arithmetic.pair s (Arithmetic.pair d (Arithmetic.pair 0 c + 1))) =
      Arithmetic.pair 0 (Arithmetic.pair 2 (Arithmetic.pair (Arithmetic.pi₁ (Arithmetic.pi₂ c))
        (proofRewriteArguments.evalArithmetic (Arithmetic.pair s (Arithmetic.pair d (Arithmetic.pi₂ (Arithmetic.pi₂ c))))))) + 1 := by
  exact evalArithmetic_formulaTransformCode_rel proofRewriteArguments s d c

@[simp] theorem evalArithmetic_proofRewriteCode_nrel (s d c : M) :
    proofRewriteCode.evalArithmetic (Arithmetic.pair s (Arithmetic.pair d (Arithmetic.pair 1 c + 1))) =
      Arithmetic.pair 1 (Arithmetic.pair 2 (Arithmetic.pair (Arithmetic.pi₁ (Arithmetic.pi₂ c))
        (proofRewriteArguments.evalArithmetic (Arithmetic.pair s (Arithmetic.pair d (Arithmetic.pi₂ (Arithmetic.pi₂ c))))))) + 1 := by
  exact evalArithmetic_formulaTransformCode_nrel proofRewriteArguments s d c

@[simp] theorem evalArithmetic_proofRewriteCode_verum (s d c : M) :
    proofRewriteCode.evalArithmetic (Arithmetic.pair s (Arithmetic.pair d (Arithmetic.pair 2 c + 1))) =
      Arithmetic.pair 2 0 + 1 := by
  exact evalArithmetic_formulaTransformCode_verum proofRewriteArguments s d c

@[simp] theorem evalArithmetic_proofRewriteCode_falsum (s d c : M) :
    proofRewriteCode.evalArithmetic (Arithmetic.pair s (Arithmetic.pair d (Arithmetic.pair 3 c + 1))) =
      Arithmetic.pair 3 0 + 1 := by
  exact evalArithmetic_formulaTransformCode_falsum proofRewriteArguments s d c

@[simp] theorem evalArithmetic_proofRewriteCode_and (s d a b : M) :
    proofRewriteCode.evalArithmetic (Arithmetic.pair s (Arithmetic.pair d (Arithmetic.pair 4 (Arithmetic.pair a b) + 1))) =
      Arithmetic.pair 4 (Arithmetic.pair
        (proofRewriteCode.evalArithmetic (Arithmetic.pair s (Arithmetic.pair d a)))
        (proofRewriteCode.evalArithmetic (Arithmetic.pair s (Arithmetic.pair d b)))) + 1 := by
  exact evalArithmetic_formulaTransformCode_and proofRewriteArguments s d a b

@[simp] theorem evalArithmetic_proofRewriteCode_or (s d a b : M) :
    proofRewriteCode.evalArithmetic (Arithmetic.pair s (Arithmetic.pair d (Arithmetic.pair 5 (Arithmetic.pair a b) + 1))) =
      Arithmetic.pair 5 (Arithmetic.pair
        (proofRewriteCode.evalArithmetic (Arithmetic.pair s (Arithmetic.pair d a)))
        (proofRewriteCode.evalArithmetic (Arithmetic.pair s (Arithmetic.pair d b)))) + 1 := by
  exact evalArithmetic_formulaTransformCode_or proofRewriteArguments s d a b

@[simp] theorem evalArithmetic_proofRewriteCode_all (s d a : M) :
    proofRewriteCode.evalArithmetic (Arithmetic.pair s (Arithmetic.pair d (Arithmetic.pair 6 a + 1))) =
      Arithmetic.pair 6 (proofRewriteCode.evalArithmetic (Arithmetic.pair s (Arithmetic.pair (d + 1) a))) + 1 := by
  exact evalArithmetic_formulaTransformCode_all proofRewriteArguments s d a

@[simp] theorem evalArithmetic_proofRewriteCode_exs (s d a : M) :
    proofRewriteCode.evalArithmetic (Arithmetic.pair s (Arithmetic.pair d (Arithmetic.pair 7 a + 1))) =
      Arithmetic.pair 7 (proofRewriteCode.evalArithmetic (Arithmetic.pair s (Arithmetic.pair (d + 1) a))) + 1 := by
  exact evalArithmetic_formulaTransformCode_exs proofRewriteArguments s d a

end PrimitiveProgram
end ZFVP
