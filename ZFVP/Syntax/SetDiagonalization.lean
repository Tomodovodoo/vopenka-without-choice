import ZFVP.Syntax.SetNumeralQuotation
import ZFVP.ModelTheory.InternalPrimitiveProgram

/-! A constructive diagonal lemma for the relational language of set theory. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory
open PrimitiveProgram

def setDiagonalBody (θ : SetTheorySemisentence 1) : SetTheorySemisentence 1 :=
  “x. ∃ y, !setDiagonalCode.formula y x ∧ !θ y”

def setFixedpoint (θ : SetTheorySemisentence 1) : SetTheorySentence :=
  setNumeralSubstitution (setDiagonalBody θ) (Encodable.encode (setDiagonalBody θ))

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem eval_setDiagonalBody (θ : SetTheorySemisentence 1) (x : V) :
    (setDiagonalBody θ).Evalb ![x] ↔ θ.Evalb ![setDiagonalCode.evalSet x] := by
  simp [setDiagonalBody, (evalSet_defined setDiagonalCode).iff]

theorem models_setFixedpoint (θ : SetTheorySemisentence 1) :
    V↓[ℒₛₑₜ] ⊧ setFixedpoint θ ↔ θ.Evalb ![(Encodable.encode (setFixedpoint θ) : V)] := by
  rw [setFixedpoint, eval_setNumeralSubstitution, eval_setDiagonalBody,
    evalSet_natCast, setDiagonalCode_encode]

theorem zf_proves_setFixedpoint (θ : SetTheorySemisentence 1) :
    𝗭𝗙 ⊢ setFixedpoint θ 🡘 setNumeralSubstitution θ (Encodable.encode (setFixedpoint θ)) := by
  apply SetTheory.provable_of_models.{0}
  intro V _ _ _
  have h := (models_setFixedpoint (V := V) θ).trans (eval_setNumeralSubstitution θ _).symm
  simpa [models_iff] using h

end ZFVP
