import ZFVP.Syntax.PrimitiveProgramTemplate
import ZFVP.Syntax.PrimitiveProgramSyntaxChecks
import ZFVP.Syntax.GeneratedAxiomEnumeration

/-! Explicit optional axiom generation from the fixed axioms and the three schema templates. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory LO.FirstOrder.Arithmetic

namespace PrimitiveProgram

def templateOptionProgram {a : ℕ} (t : MembershipTemplate a 0) : PrimitiveProgram :=
  ifZero (.comp (formulaCheck false) (.pair (.comp addition (.pair (constant a) .left)) .right))
    .zero (.comp .succ t.closedTailProgram)

def generatedAxiomProgram : PrimitiveProgram :=
  let tag := .left
  let tail := .right
  let e := .comp .right tail
  let fixed := fun φ : SetTheorySentence ↦ constant (Encodable.encode φ + 1)
  ifEqual tag (constant 0) (fixed Axiom.empty)
    (ifEqual tag (constant 1) (fixed Axiom.extentionality)
    (ifEqual tag (constant 2) (fixed Axiom.pairing)
    (ifEqual tag (constant 3) (fixed Axiom.union)
    (ifEqual tag (constant 4) (fixed Axiom.power)
    (ifEqual tag (constant 5) (fixed Axiom.infinity)
    (ifEqual tag (constant 6) (fixed Axiom.foundation)
    (ifEqual tag (constant 7) (fixed equalityBasisSentence)
    (ifEqual tag (constant 8) (.comp (templateOptionProgram separationTemplate) tail)
    (ifEqual tag (constant 9) (.comp (templateOptionProgram replacementTemplate) tail)
    (ifEqual tag (constant 10) (.comp (templateOptionProgram vopenkaTemplate) (.pair .zero e)) .zero))))))))))

def generatedAxiomCheck : PrimitiveProgram :=
  .comp equal (.pair (.comp generatedAxiomProgram .right) (.comp .succ .left))

variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem evalArithmetic_templateOptionProgram {a : ℕ} (t : MembershipTemplate a 0) (k c : M) :
    (templateOptionProgram t).evalArithmetic (Arithmetic.pair k c) =
      if (formulaCheck false).evalArithmetic (Arithmetic.pair ((a : M) + k) c) = 0 then 0
      else t.closedTailProgram.evalArithmetic (Arithmetic.pair k c) + 1 := by
  simp [templateOptionProgram]

theorem evalArithmetic_templateOptionProgram_some {a : ℕ} (t : MembershipTemplate a 0) (k c φ : M) :
    (templateOptionProgram t).evalArithmetic (Arithmetic.pair k c) = φ + 1 ↔
      ((formulaRequirement false).evalArithmetic c ≠ 0 ∧
        (formulaRequirement false).evalArithmetic c ≤ ((a : M) + k) + 1) ∧
      t.closedTailProgram.evalArithmetic (Arithmetic.pair k c) = φ := by
  rw [evalArithmetic_templateOptionProgram]
  by_cases h : (formulaCheck false).evalArithmetic (Arithmetic.pair ((a : M) + k) c) = 0
  · have hn := (evalArithmetic_formulaCheck_ne_zero false ((a : M) + k) c).not.mp (not_not.mpr h)
    simp [h, hn]
  · have hv := (evalArithmetic_formulaCheck_ne_zero false ((a : M) + k) c).mp h
    simp [h, hv]

noncomputable def arithmeticGeneratedAxiomValue (tag k c : M) : M :=
  if tag = 0 then (Encodable.encode Axiom.empty + 1 : ℕ)
  else if tag = 1 then (Encodable.encode Axiom.extentionality + 1 : ℕ)
  else if tag = 2 then (Encodable.encode Axiom.pairing + 1 : ℕ)
  else if tag = 3 then (Encodable.encode Axiom.union + 1 : ℕ)
  else if tag = 4 then (Encodable.encode Axiom.power + 1 : ℕ)
  else if tag = 5 then (Encodable.encode Axiom.infinity + 1 : ℕ)
  else if tag = 6 then (Encodable.encode Axiom.foundation + 1 : ℕ)
  else if tag = 7 then (Encodable.encode equalityBasisSentence + 1 : ℕ)
  else if tag = 8 then (templateOptionProgram separationTemplate).evalArithmetic (Arithmetic.pair k c)
  else if tag = 9 then (templateOptionProgram replacementTemplate).evalArithmetic (Arithmetic.pair k c)
  else if tag = 10 then (templateOptionProgram vopenkaTemplate).evalArithmetic (Arithmetic.pair 0 c)
  else 0

theorem evalArithmetic_generatedAxiomProgram (tag k c : M) :
    generatedAxiomProgram.evalArithmetic (Arithmetic.pair tag (Arithmetic.pair k c)) =
      arithmeticGeneratedAxiomValue tag k c := by
  simp only [generatedAxiomProgram, arithmeticGeneratedAxiomValue, evalArithmetic_ifEqual,
    evalArithmetic_left, evalArithmetic_right, evalArithmetic_comp, evalArithmetic_pair,
    evalArithmetic_zero, evalArithmetic_constant, Arithmetic.pi₁_pair, Arithmetic.pi₂_pair,
    Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat]

theorem evalArithmetic_generatedAxiomCheck (φ e : M) :
    generatedAxiomCheck.evalArithmetic (Arithmetic.pair φ e) = 1 ↔
      generatedAxiomProgram.evalArithmetic e = φ + 1 := by
  simp [generatedAxiomCheck]

end PrimitiveProgram
end ZFVP
