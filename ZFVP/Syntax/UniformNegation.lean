import ZFVP.Syntax.FormulaNegation
import ZFVP.Syntax.UniformSubformulas
import ZFVP.Syntax.UniformSyntaxTransport
import ZFVP.SetTheory.UniformFunctionOperations

/-! A shared parameter-free dictionary for internal negation. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def formulaNegationStepFormula : SetTheorySemisentence 3 :=
  f“z q p. ∀ n, n = !kpair.π₁.dfn q → ∀ φ, φ = !kpair.π₂.dfn q →
    ∀ t, t = !kpair.π₁.dfn φ → ∀ d, d = !kpair.π₂.dfn φ →
    (t = !(numeralFormula 0) ∧ z = !falsityCodeFormula) ∨
    (t ≠ !(numeralFormula 0) ∧ t = !(numeralFormula 1) ∧ z = !truthCodeFormula) ∨
    (t ≠ !(numeralFormula 0) ∧ t ≠ !(numeralFormula 1) ∧ t = !(numeralFormula 2) ∧
      z = !negAtomCodeFormula (!kpair.π₁.dfn d) (!kpair.π₂.dfn d)) ∨
    (t ≠ !(numeralFormula 0) ∧ t ≠ !(numeralFormula 1) ∧ t ≠ !(numeralFormula 2) ∧ t = !(numeralFormula 3) ∧
      z = !atomCodeFormula (!kpair.π₁.dfn d) (!kpair.π₂.dfn d)) ∨
    (t ≠ !(numeralFormula 0) ∧ t ≠ !(numeralFormula 1) ∧ t ≠ !(numeralFormula 2) ∧ t ≠ !(numeralFormula 3) ∧
      t = !(numeralFormula 4) ∧ z = !orCodeFormula
        (!value.dfn p (!kpair.dfn n (!kpair.π₁.dfn d))) (!value.dfn p (!kpair.dfn n (!kpair.π₂.dfn d)))) ∨
    (t ≠ !(numeralFormula 0) ∧ t ≠ !(numeralFormula 1) ∧ t ≠ !(numeralFormula 2) ∧ t ≠ !(numeralFormula 3) ∧
      t ≠ !(numeralFormula 4) ∧ t = !(numeralFormula 5) ∧ z = !andCodeFormula
        (!value.dfn p (!kpair.dfn n (!kpair.π₁.dfn d))) (!value.dfn p (!kpair.dfn n (!kpair.π₂.dfn d)))) ∨
    (t ≠ !(numeralFormula 0) ∧ t ≠ !(numeralFormula 1) ∧ t ≠ !(numeralFormula 2) ∧ t ≠ !(numeralFormula 3) ∧
      t ≠ !(numeralFormula 4) ∧ t ≠ !(numeralFormula 5) ∧ t = !(numeralFormula 6) ∧
        z = !existsCodeFormula (!value.dfn p (!kpair.dfn (!succ.dfn n) d))) ∨
    (t ≠ !(numeralFormula 0) ∧ t ≠ !(numeralFormula 1) ∧ t ≠ !(numeralFormula 2) ∧ t ≠ !(numeralFormula 3) ∧
      t ≠ !(numeralFormula 4) ∧ t ≠ !(numeralFormula 5) ∧ t ≠ !(numeralFormula 6) ∧
        z = !allCodeFormula (!value.dfn p (!kpair.dfn (!succ.dfn n) d)))”

def formulaNegationGraphFormula : SetTheorySemisentence 3 :=
  f“g L Γ. !IsFunction.dfn g ∧ !domain.dfn g = !formulaFamilyFormula L Γ ∧
    ∀ q ∈ !formulaFamilyFormula L Γ, !value.dfn g q = !formulaNegationStepFormula q
      (!restrict.dfn g (!predecessorsFormula (!subformulaRelationFormula (!formulaFamilyFormula L Γ))
        (!formulaFamilyFormula L Γ) q))”

def negateFormulaFormula : SetTheorySemisentence 5 :=
  f“y L Γ n φ. y = !value.dfn (!formulaNegationGraphFormula L Γ) (!kpair.dfn n φ)”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

instance formulaNegationStepFormula_defined : ℒₛₑₜ-function₂[V] formulaNegationStep via formulaNegationStepFormula :=
  ⟨fun v ↦ by
    simp only [formulaNegationStepFormula]
    simp
    unfold formulaNegationStep
    dsimp
    split <;> simp_all
    split <;> simp_all
    split <;> simp_all
    split <;> simp_all
    split <;> simp_all
    split <;> simp_all
    split <;> simp_all⟩

instance formulaNegationGraphFormula_defined : ℒₛₑₜ-function₂[V] formulaNegationGraph via formulaNegationGraphFormula :=
  ⟨fun v ↦ by
    change formulaNegationGraphFormula.Evalb v ↔ v 0 = formulaNegationGraph (v 1) (v 2)
    rw [eq_comm, formulaNegationGraph_eq_iff, totalRecursionAttempt_iff]
    simp [formulaNegationGraphFormula]⟩

instance negateFormulaFormula_defined : ℒₛₑₜ-function₄[V] negateFormula via negateFormulaFormula :=
  ⟨fun v ↦ by simp [negateFormulaFormula, negateFormula]⟩

namespace ElementaryMap

variable {W : Type*} [SetStructure W] [Nonempty W] [W↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem map_negateFormula (j : ElementaryMap V W) (L Γ n φ : V) :
    j (negateFormula L Γ n φ) = negateFormula (j L) (j Γ) (j n) (j φ) :=
  j.map_definedFunction negateFormulaFormula
    (fun v ↦ negateFormula (v 0) (v 1) (v 2) (v 3))
    (fun v ↦ negateFormula (v 0) (v 1) (v 2) (v 3)) ![L, Γ, n, φ]

end ElementaryMap
end ZFVP
