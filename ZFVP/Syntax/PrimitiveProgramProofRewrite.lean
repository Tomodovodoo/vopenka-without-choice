import ZFVP.Syntax.PrimitiveProgramFormulaTransform

/-! The proof-rule rewrite program specializes the common formula transformer. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.Arithmetic

namespace PrimitiveProgram

def proofRewriteCell : PrimitiveProgram := formulaTransformCell proofRewriteArguments

def proofRewriteBounded : PrimitiveProgram := formulaTransformBounded proofRewriteArguments

/-- Input is `(mode, (initialDepth, formulaCode))`. -/
def proofRewriteCode : PrimitiveProgram := formulaTransformCode proofRewriteArguments

variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

noncomputable def arithmeticProofRewriteValue (s d t c : M) (F : M → M → M) : M :=
  arithmeticFormulaTransformValue proofRewriteArguments s d t c F

@[simp] theorem evalArithmetic_proofRewriteCell (s D n table d : M) :
    proofRewriteCell.evalArithmetic (Arithmetic.pair
      (Arithmetic.pair (Arithmetic.pair s D) (Arithmetic.pair n table)) d) =
      if n = 0 then 0 else arithmeticProofRewriteValue s d (Arithmetic.pi₁ (n - 1)) (Arithmetic.pi₂ (n - 1))
        (fun child depth ↦ listGet.evalArithmetic (Arithmetic.pair
          (listGet.evalArithmetic (Arithmetic.pair table (n - (child + 1)))) (D - depth))) := by
  exact evalArithmetic_formulaTransformCell proofRewriteArguments s D n table d

theorem evalArithmetic_proofRewriteBounded (s D n d : M) (hd : d ≤ D) :
    proofRewriteBounded.evalArithmetic (Arithmetic.pair (Arithmetic.pair s D) (Arithmetic.pair n d)) =
      if n = 0 then 0 else arithmeticProofRewriteValue s d (Arithmetic.pi₁ (n - 1)) (Arithmetic.pi₂ (n - 1))
        (fun child depth ↦ listGet.evalArithmetic (Arithmetic.pair
          (listGet.evalArithmetic (Arithmetic.pair
            ((courseTable (indexedCourseStep proofRewriteCell)).evalArithmetic (Arithmetic.pair (Arithmetic.pair s D) n))
            (n - (child + 1)))) (D - depth))) := by
  exact evalArithmetic_formulaTransformBounded proofRewriteArguments s D n d hd

@[simp] theorem evalArithmetic_proofRewriteCode (s d n : M) :
    proofRewriteCode.evalArithmetic (Arithmetic.pair s (Arithmetic.pair d n)) =
      proofRewriteBounded.evalArithmetic (Arithmetic.pair (Arithmetic.pair s (d + n)) (Arithmetic.pair n d)) := by
  exact evalArithmetic_formulaTransformCode proofRewriteArguments s d n

theorem evalArithmetic_proofRewriteBounded_tagged (s D t c d : M) (hd : d ≤ D) :
    proofRewriteBounded.evalArithmetic (Arithmetic.pair (Arithmetic.pair s D) (Arithmetic.pair (Arithmetic.pair t c + 1) d)) =
      arithmeticProofRewriteValue s d t c
        (fun child depth ↦ proofRewriteBounded.evalArithmetic (Arithmetic.pair (Arithmetic.pair s D) (Arithmetic.pair child depth))) := by
  exact evalArithmetic_formulaTransformBounded_tagged proofRewriteArguments s D t c d hd

end PrimitiveProgram
end ZFVP
