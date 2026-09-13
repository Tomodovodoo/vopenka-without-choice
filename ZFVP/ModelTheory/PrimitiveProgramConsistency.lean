import ZFVP.ModelTheory.PrimitiveProgramAgreement
import ZFVP.Syntax.ArithmeticPrimitiveProgramStandard

/-! A program's universal rejection statement has matching arithmetic and set-theoretic meanings. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory LO.FirstOrder.Arithmetic

namespace PrimitiveProgram

def arithmeticRejectsOneSentence (c : PrimitiveProgram) : ArithmeticSentence :=
  “∀ x, ¬!c.arithmeticFormula 1 x”

def setRejectsOneSentence (c : PrimitiveProgram) : SetTheorySentence :=
  f“∀ x ∈ !isω, ¬!c.formula (!succ.dfn (!isEmpty)) x”

theorem arithmeticRejectsOneSentence_piOne (c : PrimitiveProgram) :
    Hierarchy 𝚷 1 c.arithmeticRejectsOneSentence := by
  simp [arithmeticRejectsOneSentence]

theorem eval_arithmeticRejectsOneSentence (c : PrimitiveProgram)
    {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] :
    c.arithmeticRejectsOneSentence.Evalb (![] : Fin 0 → M) ↔ ∀ x : M, c.evalArithmetic x ≠ 1 := by
  simp [arithmeticRejectsOneSentence, (evalArithmetic_defined c).iff, eq_comm]

theorem eval_arithmeticRejectsOneSentence_nat (c : PrimitiveProgram) :
    c.arithmeticRejectsOneSentence.Evalb (![] : Fin 0 → ℕ) ↔ ∀ n : ℕ, c.eval n ≠ 1 := by
  rw [eval_arithmeticRejectsOneSentence]
  simp only [evalArithmetic_nat]

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem eval_setRejectsOneSentence (c : PrimitiveProgram) :
    c.setRejectsOneSentence.Evalb (![] : Fin 0 → V) ↔ ∀ x ∈ (ω : V), c.evalSet x ≠ 1 := by
  have h1 : SetTheory.succ (∅ : V) = 1 := rfl
  simp [setRejectsOneSentence, (evalSet_defined c).iff, h1, eq_comm]

theorem rejectsOne_internalArithmetic_iff (c : PrimitiveProgram) :
    (∀ x : InternalArithmetic V, c.evalArithmetic x ≠ 1) ↔ ∀ x ∈ (ω : V), c.evalSet x ≠ 1 := by
  have hp (x : InternalArithmetic V) : c.evalArithmetic x ≠ 1 ↔ c.evalSet (internalArithmeticVal x) ≠ (1 : V) := by
    rw [ne_eq, internalArithmetic_eq, evalArithmetic_agreement, internalArithmeticVal_one]
  constructor
  · intro h t ht
    obtain ⟨x, rfl⟩ := internalArithmeticVal_surjective ht
    exact (hp x).mp (h x)
  · intro h x
    exact (hp x).mpr (h _ (internalArithmeticVal_mem x))

theorem models_arithmeticRejectsOne_translation (c : PrimitiveProgram) :
    V↓[ℒₛₑₜ] ⊧ arithmeticInZF.translate c.arithmeticRejectsOneSentence ↔ V↓[ℒₛₑₜ] ⊧ c.setRejectsOneSentence := by
  rw [internalArithmetic_translation]
  have h := (eval_arithmeticRejectsOneSentence c (M := InternalArithmetic V)).trans
    ((rejectsOne_internalArithmetic_iff c).trans (eval_setRejectsOneSentence c).symm)
  simpa only [models_iff, Semiformula.Realize, Semiformula.Evalb] using h

theorem zf_proves_rejectsOne_translation (c : PrimitiveProgram) :
    𝗭𝗙 ⊢ (arithmeticInZF.translate c.arithmeticRejectsOneSentence 🡘 c.setRejectsOneSentence) := by
  apply SetTheory.provable_of_models.{0}
  intro V _ _ _
  simpa [models_iff] using models_arithmeticRejectsOne_translation (V := V) c

end PrimitiveProgram
end ZFVP
