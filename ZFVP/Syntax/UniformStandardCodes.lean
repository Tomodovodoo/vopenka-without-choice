import ZFVP.Syntax.StandardCodeExpressions
import ZFVP.SetTheory.UniformCodingUniverse

/-! Parameter-free definitions of the internal codes of fixed external formulas. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def closedCodeExpressionFormula (e : CodeExpression 0) : SetTheorySemisentence 1 :=
  f“x. !(e.formula) (!codingUniverseFormula (!isEmpty)) x”

def encodeMembershipFormulaFormula {n : ℕ} (φ : SetTheorySemisentence n) :
    SetTheorySemisentence 1 := closedCodeExpressionFormula (membershipFormulaExpression φ)

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

instance closedCodeExpressionFormula_defined (e : CodeExpression 0) :
    ℒₛₑₜ-function₀[V] (e.eval ![]) via closedCodeExpressionFormula e :=
  ⟨fun v ↦ by simp [closedCodeExpressionFormula]⟩

instance encodeMembershipFormulaFormula_defined {n : ℕ} (φ : SetTheorySemisentence n) :
    ℒₛₑₜ-function₀[V] (encodeMembershipFormula φ) via encodeMembershipFormulaFormula φ := by
  simpa only [eval_membershipFormulaExpression, encodeMembershipFormulaFormula] using
    (closedCodeExpressionFormula_defined (V := V) (membershipFormulaExpression φ))

end ZFVP
