import ZFVP.Syntax.UniformParameters
import ZFVP.SetTheory.UniformFunctionOperations

/-! A shared parameter-free formula for the internal term evaluation graph. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def subtermRelationFormula : SetTheorySemisentence 2 :=
  f“R T. ∀ p, p ∈ R ↔ p ∈ !prod.dfn T T ∧ ∃ f args,
    !kpair.π₂.dfn p = !functionTermCodeFormula f args ∧ !kpair.π₁.dfn p ∈ !range.dfn args”

def termStepFromStateFormula : SetTheorySemisentence 4 :=
  f“z A t previous.
    (!kpair.π₁.dfn t = !(numeralFormula 0) ∧
      z = !value.dfn (!kpair.π₁.dfn (!kpair.π₂.dfn A)) (!kpair.π₂.dfn t)) ∨
    (!kpair.π₁.dfn t ≠ !(numeralFormula 0) ∧ !kpair.π₁.dfn t = !(numeralFormula 1) ∧
      z = !value.dfn (!kpair.π₂.dfn (!kpair.π₂.dfn A)) (!kpair.π₂.dfn t)) ∨
    (!kpair.π₁.dfn t ≠ !(numeralFormula 0) ∧ !kpair.π₁.dfn t ≠ !(numeralFormula 1) ∧
      z = !value.dfn (!value.dfn (!structureFunctionsFormula (!kpair.π₁.dfn A))
        (!kpair.π₁.dfn (!kpair.π₂.dfn t)))
        (!composeFormula (!kpair.π₂.dfn (!kpair.π₂.dfn t)) previous))”

def packedTermEvaluationFormula : SetTheorySemisentence 4 :=
  f“g P n b. !IsFunction.dfn g ∧
    !domain.dfn g = !termSetFormula (!satLanguageFormula P) (!satVariablesFormula P) n ∧
    ∀ t ∈ !termSetFormula (!satLanguageFormula P) (!satVariablesFormula P) n,
      !value.dfn g t = !termStepFromStateFormula
        (!kpair.dfn (!satStructureFormula P) (!kpair.dfn b (!satFreeAssignmentFormula P))) t
        (!restrict.dfn g (!predecessorsFormula
          (!subtermRelationFormula (!termSetFormula (!satLanguageFormula P) (!satVariablesFormula P) n))
          (!termSetFormula (!satLanguageFormula P) (!satVariablesFormula P) n) t))”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def termStepFromState (A t previous : V) : V :=
  termEvaluationStep (kpair.π₁ A) (kpair.π₁ (kpair.π₂ A)) (kpair.π₂ (kpair.π₂ A)) t previous

instance subtermRelationFormula_defined : ℒₛₑₜ-function₁[V] subtermRelation via subtermRelationFormula :=
  ⟨fun v ↦ by
    change subtermRelationFormula.Evalb v ↔ v 0 = subtermRelation (v 1)
    rw [mem_ext_iff]
    simp [subtermRelationFormula, subtermRelation]⟩

instance termStepFromStateFormula_defined : ℒₛₑₜ-function₃[V] termStepFromState via termStepFromStateFormula :=
  ⟨fun v ↦ by
    by_cases h0 : kpair.π₁ (v 2) = 0 <;> by_cases h1 : kpair.π₁ (v 2) = 1 <;>
      simp [termStepFromStateFormula, termStepFromState, termEvaluationStep, h0, h1]⟩

instance packedTermEvaluationFormula_defined :
    ℒₛₑₜ-function₃[V] packedTermEvaluation via packedTermEvaluationFormula :=
  ⟨fun v ↦ by
    change packedTermEvaluationFormula.Evalb v ↔ v 0 = packedTermEvaluation (v 1) (v 2) (v 3)
    rw [eq_comm]
    unfold packedTermEvaluation
    rw [termEvaluation_eq_iff, totalRecursionAttempt_iff]
    simp [packedTermEvaluationFormula, termStepFromState]⟩

end ZFVP
