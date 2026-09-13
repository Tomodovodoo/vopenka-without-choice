import ZFVP.Syntax.PrimitiveProgramGeneratedAxioms
import ZFVP.Syntax.PrimitiveProgramLKCertificate

/-! A primitive recursive checker for LK proofs from enumerated ZF+VP axioms. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.Arithmetic

namespace PrimitiveProgram

def generatedAxiomRowsCheck : PrimitiveProgram :=
  listAll (.comp equal (.pair (.comp generatedAxiomCheck .right) (constant 1)))

def negatedAxiomRow : PrimitiveProgram := .comp negateCode (.comp .left .right)

def generatedTheorySequent : PrimitiveProgram :=
  listCons .left (.comp (listMap negatedAxiomRow) (.pair .zero .right))

def generatedTheoryProofCheck : PrimitiveProgram :=
  let rows := .comp .left .right
  let cert := .comp .right .right
  allOf [
    .comp equal (.pair (.comp (formulaCheck false) (.pair .zero .left)) (constant 1)),
    .comp equal (.pair (.comp generatedAxiomRowsCheck (.pair .zero rows)) (constant 1)),
    .comp equal (.pair (.comp lkProofCheck
      (.pair (.comp generatedTheorySequent (.pair .left rows)) cert)) (constant 1))]

variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem evalArithmetic_generatedAxiomRowsCheck (z rows : M) :
    generatedAxiomRowsCheck.evalArithmetic (Arithmetic.pair z rows) = 1 ↔
      ∀ i < listLength.evalArithmetic rows,
        generatedAxiomCheck.evalArithmetic (listGet.evalArithmetic (Arithmetic.pair rows i)) = 1 := by
  simp [generatedAxiomRowsCheck]

@[simp] theorem evalArithmetic_negatedAxiomRow (z row : M) :
    negatedAxiomRow.evalArithmetic (Arithmetic.pair z row) =
      negateCode.evalArithmetic (Arithmetic.pi₁ row) := by
  simp [negatedAxiomRow]

theorem evalArithmetic_generatedTheorySequent (φ rows : M) :
    generatedTheorySequent.evalArithmetic (Arithmetic.pair φ rows) =
      Arithmetic.pair φ ((listMap negatedAxiomRow).evalArithmetic (Arithmetic.pair 0 rows)) + 1 := by
  simp [generatedTheorySequent, listCons]

theorem evalArithmetic_generatedTheoryProofCheck (φ rows p : M) :
    generatedTheoryProofCheck.evalArithmetic (Arithmetic.pair φ (Arithmetic.pair rows p)) = 1 ↔
      (formulaCheck false).evalArithmetic (Arithmetic.pair 0 φ) = 1 ∧
      generatedAxiomRowsCheck.evalArithmetic (Arithmetic.pair 0 rows) = 1 ∧
      lkProofCheck.evalArithmetic (Arithmetic.pair
        (generatedTheorySequent.evalArithmetic (Arithmetic.pair φ rows)) p) = 1 := by
  by_cases hf : (formulaCheck false).evalArithmetic (Arithmetic.pair 0 φ) = 1 <;>
    by_cases ha : generatedAxiomRowsCheck.evalArithmetic (Arithmetic.pair 0 rows) = 1 <;>
    by_cases hp : lkProofCheck.evalArithmetic (Arithmetic.pair
      (generatedTheorySequent.evalArithmetic (Arithmetic.pair φ rows)) p) = 1 <;>
      simp [generatedTheoryProofCheck, allOf, hf, ha, hp]

end PrimitiveProgram
end ZFVP
