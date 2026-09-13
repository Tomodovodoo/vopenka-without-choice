import ZFVP.Syntax.PrimitiveProgramFormulaTransformEquations
import ZFVP.Syntax.PrimitiveProgramListLength

/-! Explicit capture-avoiding bound-variable renaming from an internally finite index table. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.Arithmetic

namespace PrimitiveProgram

def reindexVariable : PrimitiveProgram :=
  let r := .left
  let d := .comp .left .right
  let i := .comp .right .right
  let j := .comp subtraction (.pair i d)
  let value := ifLess j (.comp listLength r) (.comp listGet (.pair r j)) j
  ifLess i d i (.comp addition (.pair value d))

def reindexTerm : PrimitiveProgram :=
  tagged 0 (.comp reindexVariable (.pair .left (.pair (.comp .left .right)
    (.comp listTail (.comp .right .right)))))

def reindexArguments : PrimitiveProgram :=
  let r := .left
  let d := .comp .left .right
  let c := .comp .right .right
  vectorTwo
    (.comp reindexTerm (.pair r (.pair d (.comp listHead c))))
    (.comp reindexTerm (.pair r (.pair d (.comp listHead (.comp listTail c)))))

def reindexCode : PrimitiveProgram := formulaTransformCode reindexArguments

variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

noncomputable def arithmeticReindexVariable (r d i : M) : M :=
  if i < d then i else
    (if i - d < listLength.evalArithmetic r then
      listGet.evalArithmetic (Arithmetic.pair r (i - d)) else i - d) + d

noncomputable def arithmeticReindexTerm (r d c : M) : M :=
  Arithmetic.pair 0 (arithmeticReindexVariable r d (Arithmetic.pi₂ (c - 1))) + 1

@[simp] theorem evalArithmetic_reindexVariable (r d i : M) :
    reindexVariable.evalArithmetic (Arithmetic.pair r (Arithmetic.pair d i)) =
      arithmeticReindexVariable r d i := by
  simp [reindexVariable, arithmeticReindexVariable]

@[simp] theorem evalArithmetic_reindexTerm (r d c : M) :
    reindexTerm.evalArithmetic (Arithmetic.pair r (Arithmetic.pair d c)) =
      arithmeticReindexTerm r d c := by
  simp [reindexTerm, arithmeticReindexTerm]

@[simp] theorem evalArithmetic_reindexArguments (r d c : M) :
    reindexArguments.evalArithmetic (Arithmetic.pair r (Arithmetic.pair d c)) =
      Arithmetic.pair (arithmeticReindexTerm r d (listHead.evalArithmetic c))
        (Arithmetic.pair (arithmeticReindexTerm r d (listHead.evalArithmetic (listTail.evalArithmetic c))) 0 + 1) + 1 := by
  simp [reindexArguments]

end PrimitiveProgram
end ZFVP
