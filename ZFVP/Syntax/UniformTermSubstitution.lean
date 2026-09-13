import ZFVP.Syntax.TermSubstitution
import ZFVP.Syntax.UniformTermEvaluation
import ZFVP.Syntax.UniformSyntaxTransport

/-! One parameter-free definition of term substitution in every ZF model. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

@[simp] theorem eval_nestFormulaeFunc_five {L : Language} {ξ M : Type*} [Structure L M]
    {m : ℕ} {z : M} {e : Fin m → M} {f : ξ → M} {φ : Semiformula L ξ 6}
    {ψ₁ ψ₂ ψ₃ ψ₄ ψ₅ : Semiformula L ξ (m + 1)} :
    Semiformula.Eval (z :> e) f (φ.nestFormulaeFunc ![ψ₁, ψ₂, ψ₃, ψ₄, ψ₅]) ↔
      ∀ x₁, Semiformula.Eval (x₁ :> e) f ψ₁ →
      ∀ x₂, Semiformula.Eval (x₂ :> e) f ψ₂ →
      ∀ x₃, Semiformula.Eval (x₃ :> e) f ψ₃ →
      ∀ x₄, Semiformula.Eval (x₄ :> e) f ψ₄ →
      ∀ x₅, Semiformula.Eval (x₅ :> e) f ψ₅ → Semiformula.Eval ![z, x₁, x₂, x₃, x₄, x₅] f φ := by
  simp only [Semiformula.eval_nestFormulaeFunc, Matrix.vecForall_iff, Fin.forall_fin_succ,
    Fin.forall_fin_zero, Matrix.cons_val_zero, Matrix.cons_val_succ, and_true, and_imp,
    Matrix.empty_eq, forall_const]
  constructor
  · intro h x₁ h₁ x₂ h₂ x₃ h₃ x₄ h₄ x₅ h₅
    exact h x₁ x₂ x₃ x₄ x₅ h₁ h₂ h₃ h₄ h₅
  · intro h x₁ x₂ x₃ x₄ x₅ h₁ h₂ h₃ h₄ h₅
    exact h x₁ h₁ x₂ h₂ x₃ h₃ x₄ h₄ x₅ h₅

def termSubstitutionStepFormula : SetTheorySemisentence 5 :=
  f“z b e t p.
    (!kpair.π₁.dfn t = !(numeralFormula 0) ∧ z = !value.dfn b (!kpair.π₂.dfn t)) ∨
    (!kpair.π₁.dfn t ≠ !(numeralFormula 0) ∧ !kpair.π₁.dfn t = !(numeralFormula 1) ∧
      z = !value.dfn e (!kpair.π₂.dfn t)) ∨
    (!kpair.π₁.dfn t ≠ !(numeralFormula 0) ∧ !kpair.π₁.dfn t ≠ !(numeralFormula 1) ∧
      z = !functionTermCodeFormula (!kpair.π₁.dfn (!kpair.π₂.dfn t))
        (!composeFormula (!kpair.π₂.dfn (!kpair.π₂.dfn t)) p))”

def termSubstitutionFormula : SetTheorySemisentence 6 :=
  f“g L Γ n b e. !IsFunction.dfn g ∧ !domain.dfn g = !termSetFormula L Γ n ∧
    ∀ t ∈ !termSetFormula L Γ n, !value.dfn g t = !termSubstitutionStepFormula b e t
      (!restrict.dfn g (!predecessorsFormula (!subtermRelationFormula (!termSetFormula L Γ n))
        (!termSetFormula L Γ n) t))”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

instance termSubstitutionStepFormula_defined :
    ℒₛₑₜ-function₄[V] termSubstitutionStep via termSubstitutionStepFormula :=
  ⟨fun v ↦ by
    by_cases h0 : kpair.π₁ (v 3) = 0 <;> by_cases h1 : kpair.π₁ (v 3) = 1 <;>
      simp [termSubstitutionStepFormula, termSubstitutionStep, h0, h1]⟩

instance termSubstitutionFormula_defined :
    ℒₛₑₜ-function₅[V] termSubstitution via termSubstitutionFormula :=
  ⟨fun v ↦ by
    change termSubstitutionFormula.Evalb v ↔ v 0 = termSubstitution (v 1) (v 2) (v 3) (v 4) (v 5)
    rw [eq_comm, termSubstitution_eq_iff, totalRecursionAttempt_iff]
    simp [termSubstitutionFormula]⟩

namespace ElementaryMap

variable {W : Type*} [SetStructure W] [Nonempty W] [W↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem map_termSubstitution (j : ElementaryMap V W) (L Γ n b e : V) :
    j (termSubstitution L Γ n b e) = termSubstitution (j L) (j Γ) (j n) (j b) (j e) :=
  j.map_definedFunction termSubstitutionFormula
    (fun v ↦ termSubstitution (v 0) (v 1) (v 2) (v 3) (v 4))
    (fun v ↦ termSubstitution (v 0) (v 1) (v 2) (v 3) (v 4)) ![L, Γ, n, b, e]

end ElementaryMap

end ZFVP
