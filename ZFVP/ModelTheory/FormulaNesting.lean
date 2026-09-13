import Foundation.FirstOrder.Basic.Definability

/-! Evaluation support for five- and seven-argument relation formulas. -/

namespace ZFVP

open LO LO.FirstOrder

variable {L : Language} {ξ M : Type*} [Structure L M]
    {m : ℕ} {e : Fin m → M} {f : ξ → M}

@[simp] theorem eval_nestFormulae_five {φ : Semiformula L ξ 5}
    {ψ₁ ψ₂ ψ₃ ψ₄ ψ₅ : Semiformula L ξ (m + 1)} :
    Semiformula.Eval e f (φ.nestFormulae ![ψ₁, ψ₂, ψ₃, ψ₄, ψ₅]) ↔
      ∀ x₁, Semiformula.Eval (x₁ :> e) f ψ₁ →
      ∀ x₂, Semiformula.Eval (x₂ :> e) f ψ₂ →
      ∀ x₃, Semiformula.Eval (x₃ :> e) f ψ₃ →
      ∀ x₄, Semiformula.Eval (x₄ :> e) f ψ₄ →
      ∀ x₅, Semiformula.Eval (x₅ :> e) f ψ₅ → Semiformula.Eval ![x₁, x₂, x₃, x₄, x₅] f φ := by
  simp [Semiformula.eval_nestFormulae, Matrix.vecForall_iff, Matrix.empty_eq,
    Fin.forall_fin_succ, Matrix.cons_val_zero, Matrix.cons_val_succ]
  grind

@[simp] theorem eval_nestFormulae_seven {φ : Semiformula L ξ 7}
    {ψ₁ ψ₂ ψ₃ ψ₄ ψ₅ ψ₆ ψ₇ : Semiformula L ξ (m + 1)} :
    Semiformula.Eval e f (φ.nestFormulae ![ψ₁, ψ₂, ψ₃, ψ₄, ψ₅, ψ₆, ψ₇]) ↔
      ∀ x₁, Semiformula.Eval (x₁ :> e) f ψ₁ →
      ∀ x₂, Semiformula.Eval (x₂ :> e) f ψ₂ →
      ∀ x₃, Semiformula.Eval (x₃ :> e) f ψ₃ →
      ∀ x₄, Semiformula.Eval (x₄ :> e) f ψ₄ →
      ∀ x₅, Semiformula.Eval (x₅ :> e) f ψ₅ →
      ∀ x₆, Semiformula.Eval (x₆ :> e) f ψ₆ →
      ∀ x₇, Semiformula.Eval (x₇ :> e) f ψ₇ →
        Semiformula.Eval ![x₁, x₂, x₃, x₄, x₅, x₆, x₇] f φ := by
  simp [Semiformula.eval_nestFormulae, Matrix.vecForall_iff, Matrix.empty_eq,
    Fin.forall_fin_succ, Matrix.cons_val_zero, Matrix.cons_val_succ]
  grind

end ZFVP


