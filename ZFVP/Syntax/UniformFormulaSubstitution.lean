import ZFVP.Syntax.FormulaSubstitutionDefinability
import ZFVP.Syntax.UniformSubstitutionStates
import ZFVP.Syntax.UniformSubformulas

/-! A shared parameter-free dictionary for the full internal formula substitution graph. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def formulaDepthDomainFormula : SetTheorySemisentence 3 :=
  f“D L Γ. D = !prod.dfn (!formulaFamilyFormula L Γ) (!isω)”

def formulaDepthRelationFormula : SetTheorySemisentence 2 :=
  f“R D. ∀ p, p ∈ R ↔ p ∈ !prod.dfn D D ∧
    !immediateSubformulaFormula (!kpair.π₁.dfn (!kpair.π₁.dfn p)) (!kpair.π₁.dfn (!kpair.π₂.dfn p))”

def substitutedArgumentsFormula : SetTheorySemisentence 6 :=
  f“z L Γ G q args. z = !composeFormula args
    (!termSubstitutionFormula L Γ (!kpair.π₁.dfn (!kpair.π₁.dfn q))
      (!stateBoundFormula (!value.dfn G (!kpair.π₂.dfn q)))
      (!stateFreeFormula (!value.dfn G (!kpair.π₂.dfn q))))”

def substitutionChildFormula : SetTheorySemisentence 3 :=
  f“p q φ. p = !kpair.dfn (!kpair.dfn (!kpair.π₁.dfn (!kpair.π₁.dfn q)) φ) (!kpair.π₂.dfn q)”

def substitutionBodyFormula : SetTheorySemisentence 3 :=
  f“p q φ. p = !kpair.dfn (!kpair.dfn (!succ.dfn (!kpair.π₁.dfn (!kpair.π₁.dfn q))) φ)
    (!succ.dfn (!kpair.π₂.dfn q))”

def formulaSubstitutionStepFormula : SetTheorySemisentence 6 :=
  f“z L Γ G q p. ∀ φ, φ = !kpair.π₂.dfn (!kpair.π₁.dfn q) →
    ∀ t, t = !kpair.π₁.dfn φ → ∀ d, d = !kpair.π₂.dfn φ →
    (t = !(numeralFormula 0) ∧ z = !truthCodeFormula) ∨
    (t ≠ !(numeralFormula 0) ∧ t = !(numeralFormula 1) ∧ z = !falsityCodeFormula) ∨
    (t ≠ !(numeralFormula 0) ∧ t ≠ !(numeralFormula 1) ∧ t = !(numeralFormula 2) ∧
      z = !atomCodeFormula (!kpair.π₁.dfn d) (!substitutedArgumentsFormula L Γ G q (!kpair.π₂.dfn d))) ∨
    (t ≠ !(numeralFormula 0) ∧ t ≠ !(numeralFormula 1) ∧ t ≠ !(numeralFormula 2) ∧ t = !(numeralFormula 3) ∧
      z = !negAtomCodeFormula (!kpair.π₁.dfn d) (!substitutedArgumentsFormula L Γ G q (!kpair.π₂.dfn d))) ∨
    (t ≠ !(numeralFormula 0) ∧ t ≠ !(numeralFormula 1) ∧ t ≠ !(numeralFormula 2) ∧ t ≠ !(numeralFormula 3) ∧
      t = !(numeralFormula 4) ∧ z = !andCodeFormula
        (!value.dfn p (!substitutionChildFormula q (!kpair.π₁.dfn d)))
        (!value.dfn p (!substitutionChildFormula q (!kpair.π₂.dfn d)))) ∨
    (t ≠ !(numeralFormula 0) ∧ t ≠ !(numeralFormula 1) ∧ t ≠ !(numeralFormula 2) ∧ t ≠ !(numeralFormula 3) ∧
      t ≠ !(numeralFormula 4) ∧ t = !(numeralFormula 5) ∧ z = !orCodeFormula
        (!value.dfn p (!substitutionChildFormula q (!kpair.π₁.dfn d)))
        (!value.dfn p (!substitutionChildFormula q (!kpair.π₂.dfn d)))) ∨
    (t ≠ !(numeralFormula 0) ∧ t ≠ !(numeralFormula 1) ∧ t ≠ !(numeralFormula 2) ∧ t ≠ !(numeralFormula 3) ∧
      t ≠ !(numeralFormula 4) ∧ t ≠ !(numeralFormula 5) ∧ t = !(numeralFormula 6) ∧
        z = !allCodeFormula (!value.dfn p (!substitutionBodyFormula q d))) ∨
    (t ≠ !(numeralFormula 0) ∧ t ≠ !(numeralFormula 1) ∧ t ≠ !(numeralFormula 2) ∧ t ≠ !(numeralFormula 3) ∧
      t ≠ !(numeralFormula 4) ∧ t ≠ !(numeralFormula 5) ∧ t ≠ !(numeralFormula 6) ∧
        z = !existsCodeFormula (!value.dfn p (!substitutionBodyFormula q d)))”

def formulaSubstitutionGraphFormula : SetTheorySemisentence 4 :=
  f“g L Γ G. !IsFunction.dfn g ∧ !domain.dfn g = !formulaDepthDomainFormula L Γ ∧
    ∀ q ∈ !formulaDepthDomainFormula L Γ, !value.dfn g q = !formulaSubstitutionStepFormula L Γ G q
      (!restrict.dfn g (!predecessorsFormula (!formulaDepthRelationFormula (!formulaDepthDomainFormula L Γ))
        (!formulaDepthDomainFormula L Γ) q))”

def substituteFormulaFormula : SetTheorySemisentence 6 :=
  f“y L Γ Δ s φ. y = !value.dfn (!formulaSubstitutionGraphFormula L Γ (!substitutionStatesFormula L Δ s))
    (!kpair.dfn (!kpair.dfn (!stateSourceFormula s) φ) (!(numeralFormula 0)))”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

instance formulaDepthDomainFormula_defined : ℒₛₑₜ-function₂[V] formulaDepthDomain via formulaDepthDomainFormula :=
  ⟨fun v ↦ by simp [formulaDepthDomainFormula, formulaDepthDomain]⟩

instance formulaDepthRelationFormula_defined : ℒₛₑₜ-function₁[V] formulaDepthRelation via formulaDepthRelationFormula :=
  ⟨fun v ↦ by
    change formulaDepthRelationFormula.Evalb v ↔ v 0 = formulaDepthRelation (v 1)
    rw [mem_ext_iff]
    simp [formulaDepthRelationFormula, formulaDepthRelation]⟩

instance substitutedArgumentsFormula_defined : ℒₛₑₜ-function₅[V] substitutedArguments via substitutedArgumentsFormula :=
  ⟨fun v ↦ by simp [substitutedArgumentsFormula, substitutedArguments]⟩

instance substitutionChildFormula_defined : ℒₛₑₜ-function₂[V] substitutionChild via substitutionChildFormula :=
  ⟨fun v ↦ by simp [substitutionChildFormula, substitutionChild]⟩

instance substitutionBodyFormula_defined : ℒₛₑₜ-function₂[V] substitutionBody via substitutionBodyFormula :=
  ⟨fun v ↦ by simp [substitutionBodyFormula, substitutionBody]⟩

instance formulaSubstitutionStepFormula_defined :
    ℒₛₑₜ-function₅[V] formulaSubstitutionStep via formulaSubstitutionStepFormula :=
  ⟨fun v ↦ by
    simp only [formulaSubstitutionStepFormula]
    simp
    unfold formulaSubstitutionStep
    dsimp
    split <;> simp_all
    split <;> simp_all
    split <;> simp_all
    split <;> simp_all
    split <;> simp_all
    split <;> simp_all
    split <;> simp_all⟩

instance formulaSubstitutionGraphFormula_defined :
    ℒₛₑₜ-function₃[V] formulaSubstitutionGraph via formulaSubstitutionGraphFormula :=
  ⟨fun v ↦ by
    change formulaSubstitutionGraphFormula.Evalb v ↔ v 0 = formulaSubstitutionGraph (v 1) (v 2) (v 3)
    rw [eq_comm, formulaSubstitutionGraph_eq_iff, totalRecursionAttempt_iff]
    simp [formulaSubstitutionGraphFormula]⟩

instance substituteFormulaFormula_defined : ℒₛₑₜ-function₅[V] substituteFormula via substituteFormulaFormula :=
  ⟨fun v ↦ by simp [substituteFormulaFormula, substituteFormula]⟩

end ZFVP
