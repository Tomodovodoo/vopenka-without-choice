import ZFVP.ModelTheory.InternalNaturalUnpairing
import ZFVP.Syntax.ArithmeticPrimitiveProgramEquations

/-! Graphs of arithmetic functions transferred to ZF's internal omega. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory LO.FirstOrder.Arithmetic

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

instance internalArithmetic_models_ISigmaOne : (InternalArithmetic V)↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ :=
  ModelsTheory.of_provably_subtheory (InternalArithmetic V) 𝗜𝚺₁ 𝗣𝗔 inferInstance

theorem internalArithmetic_evalb_translation {n : ℕ} (φ : ArithmeticSemisentence n)
    (b : Fin n → InternalArithmetic V) :
    (arithmeticInZF.translate φ).Evalb (internalArithmeticVal ∘ b) ↔ φ.Evalb b := by
  have h := internalArithmetic_eval_translation φ b Empty.elim
  have he : (internalArithmeticVal ∘ (Empty.elim : Empty → InternalArithmetic V)) = Empty.elim := by
    funext i; cases i
  rw [he] at h
  exact h

theorem internalArithmetic_graph_translation (φ : 𝚺₁.Semisentence 2)
    (F : InternalArithmetic V → InternalArithmetic V) (hF : 𝚺₁.DefinedFunction₁ F φ)
    (x : InternalArithmetic V) {y : V} (hy : y ∈ (ω : V)) :
    (arithmeticInZF.translate φ.val).Evalb ![y, internalArithmeticVal x] ↔ y = internalArithmeticVal (F x) := by
  obtain ⟨u, rfl⟩ := internalArithmeticVal_surjective hy
  have hv : internalArithmeticVal ∘ ![u, x] = ![internalArithmeticVal u, internalArithmeticVal x] := by
    funext i; fin_cases i <;> rfl
  have h := internalArithmetic_evalb_translation φ.val ![u, x]
  rw [hv] at h
  exact h.trans (hF.iff.trans (internalArithmetic_eq u (F x)))

end ZFVP
