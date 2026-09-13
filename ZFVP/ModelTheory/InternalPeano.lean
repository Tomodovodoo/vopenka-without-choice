import ZFVP.ModelTheory.InternalPeanoMinus
import Foundation.FirstOrder.Arithmetic.Schemata

/-! Full first-order induction in ZF's internal natural-number structure. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory LO.FirstOrder.Arithmetic

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem internalArithmetic_eval_translation_one {ξ : Type*} (φ : ArithmeticSemiformula ξ 1)
    (x : InternalArithmetic V) (e : ξ → InternalArithmetic V) :
    (arithmeticInZF.translate φ).Eval ![internalArithmeticVal x] (internalArithmeticVal ∘ e) ↔
      φ.Eval ![x] e := by
  have hv : internalArithmeticVal ∘ ![x] = ![internalArithmeticVal x] := by
    funext i; fin_cases i; rfl
  exact hv ▸ internalArithmetic_eval_translation φ ![x] e

theorem internalArithmetic_induction_eval {ξ : Type*} (φ : ArithmeticSemiformula ξ 1)
    (e : ξ → InternalArithmetic V) (h0 : φ.Eval ![0] e)
    (hs : ∀ x, φ.Eval ![x] e → φ.Eval ![x + 1] e) :
    ∀ x : InternalArithmetic V, φ.Eval ![x] e := by
  let P : V → Prop := fun n ↦ (arithmeticInZF.translate φ).Eval ![n] (internalArithmeticVal ∘ e)
  have hP : Language.Definable ℒₛₑₜ (fun v : Fin 1 → V ↦ P (v 0)) :=
    ⟨(Rew.rewriteMap (internalArithmeticVal ∘ e)) ▹ arithmeticInZF.translate φ,
      fun v ↦ by
        have hv : v = ![v 0] := by funext i; fin_cases i; rfl
        simp only [Semiformula.eval_rewriteMap]
        change (arithmeticInZF.translate φ).Eval v (internalArithmeticVal ∘ e) ↔ _
        rw [hv]
        rfl⟩
  have hb : P 0 := by
    simpa only [P, internalArithmeticVal_zero] using
      (internalArithmetic_eval_translation_one φ 0 e).mpr h0
  have hstep : ∀ n ∈ (ω : V), P n → P (succ n) := by
    intro n hn ih
    obtain ⟨x, rfl⟩ := internalArithmeticVal_surjective hn
    have hx := (internalArithmetic_eval_translation_one φ x e).mp ih
    have hx1 := (internalArithmetic_eval_translation_one φ (x + 1) e).mpr (hs x hx)
    simpa only [P, internalArithmeticVal_add, internalArithmeticVal_one,
      ordinalAdd_one_natural (internalArithmeticVal_mem x)] using hx1
  intro x
  exact (internalArithmetic_eval_translation_one φ x e).mp
    (naturalNumber_induction P hP hb hstep _ (internalArithmeticVal_mem x))

instance internalArithmetic_models_Peano : (InternalArithmetic V)↓[ℒₒᵣ] ⊧* 𝗣𝗔 := by
  apply models_theory_iff.mpr
  intro ψ hψ
  rcases hψ with hψ | ⟨φ, _, rfl⟩
  · exact Theory.models (InternalArithmetic V) 𝗣𝗔⁻ hψ
  · simpa [models_iff, Semiformula.eval_univCl, succInd, Semiformula.eval_substs,
      Matrix.constant_eq_singleton] using internalArithmetic_induction_eval (V := V) φ

abbrev peanoInZF : DirectInterpretation 𝗭𝗙 𝗣𝗔 where
  trln := arithmeticInZF
  interpret_theory φ hφ := by
    apply SetTheory.provable_of_models.{0}
    intro V _ _ _
    exact (internalArithmetic_translation φ).mpr (Theory.models (InternalArithmetic V) 𝗣𝗔 hφ)

end ZFVP
