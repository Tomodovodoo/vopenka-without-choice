import ZFVP.Syntax.PrimitiveProgramTheoryProof

/-! The arithmetic consistency sentence of the explicit generated-theory proof checker. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory LO.FirstOrder.Arithmetic

def programZFVPRefutation : PrimitiveProgram :=
  .comp PrimitiveProgram.generatedTheoryProofCheck
    (.pair (PrimitiveProgram.constant (Encodable.encode (⊥ : SetTheorySentence))) PrimitiveProgram.identity)

def programZFVPRefutationFormula : 𝚺₁.Semisentence 1 :=
  .mkSigma “p. !programZFVPRefutation.arithmeticFormula 1 p”

def programZFVPConsistencySentence : ArithmeticSentence := ∀¹ ∼programZFVPRefutationFormula.val

theorem programZFVPConsistencySentence_piOne : Hierarchy 𝚷 1 programZFVPConsistencySentence := by
  simp [programZFVPConsistencySentence]

variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem evalArithmetic_programZFVPRefutation (p : M) :
    programZFVPRefutation.evalArithmetic p = PrimitiveProgram.generatedTheoryProofCheck.evalArithmetic
      (Arithmetic.pair (Encodable.encode (⊥ : SetTheorySentence) : M) p) := by
  simp [programZFVPRefutation]

theorem eval_programZFVPRefutationFormula (p : M) :
    programZFVPRefutationFormula.val.Evalb ![p] ↔ programZFVPRefutation.evalArithmetic p = 1 := by
  simp [programZFVPRefutationFormula, (PrimitiveProgram.evalArithmetic_defined programZFVPRefutation).iff, eq_comm]

theorem eval_programZFVPConsistencySentence :
    programZFVPConsistencySentence.Evalb (![] : Fin 0 → M) ↔
      ∀ p : M, programZFVPRefutation.evalArithmetic p ≠ 1 := by
  simp only [programZFVPConsistencySentence, Semiformula.Evalb, Semiformula.eval_all,
    LogicalConnective.HomClass.map_neg, LogicalConnective.Prop.neg_eq]
  change (∀ p : M, ¬programZFVPRefutationFormula.val.Evalb ![p]) ↔ _
  simp only [eval_programZFVPRefutationFormula]

end ZFVP
