import ZFVP.Syntax.UniformTermEvaluation
import ZFVP.Syntax.UniformAssignments
import ZFVP.Syntax.UniformSubformulas

/-! Shared parameter-free formulas for internal satisfaction in arbitrary coded structures. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def packedEvaluatedArgumentsFormula : SetTheorySemisentence 4 :=
  f“y P q args. y = !composeFormula args
    (!packedTermEvaluationFormula P (!kpair.π₁.dfn q) (!kpair.π₂.dfn q))”

def packedAtomicHoldsFormula : SetTheorySemisentence 3 :=
  f“P q a. (!kpair.π₁.dfn a = !isEmpty ∧
    !value.dfn (!packedEvaluatedArgumentsFormula P q (!kpair.π₂.dfn a)) (!(numeralFormula 0)) =
    !value.dfn (!packedEvaluatedArgumentsFormula P q (!kpair.π₂.dfn a)) (!(numeralFormula 1))) ∨
    ∃ s ∈ !relationSymbolsFormula (!satLanguageFormula P), !kpair.π₁.dfn a = !relationTokenFormula s ∧
      !packedEvaluatedArgumentsFormula P q (!kpair.π₂.dfn a) ∈
        !value.dfn (!structureRelationsFormula (!satStructureFormula P)) s”

def packedSatisfactionStepHoldsFormula : SetTheorySemisentence 4 :=
  f“P p previous b. !kpair.π₂.dfn p = !truthCodeFormula ∨
    (∃ r args, !kpair.π₂.dfn p = !atomCodeFormula r args ∧
      !packedAtomicHoldsFormula P (!kpair.dfn (!kpair.π₁.dfn p) b) (!kpair.dfn r args)) ∨
    (∃ r args, !kpair.π₂.dfn p = !negAtomCodeFormula r args ∧
      ¬!packedAtomicHoldsFormula P (!kpair.dfn (!kpair.π₁.dfn p) b) (!kpair.dfn r args)) ∨
    (∃ φ ψ, !kpair.π₂.dfn p = !andCodeFormula φ ψ ∧
      b ∈ !value.dfn previous (!kpair.dfn (!kpair.π₁.dfn p) φ) ∧
      b ∈ !value.dfn previous (!kpair.dfn (!kpair.π₁.dfn p) ψ)) ∨
    (∃ φ ψ, !kpair.π₂.dfn p = !orCodeFormula φ ψ ∧
      (b ∈ !value.dfn previous (!kpair.dfn (!kpair.π₁.dfn p) φ) ∨
      b ∈ !value.dfn previous (!kpair.dfn (!kpair.π₁.dfn p) ψ))) ∨
    (∃ φ, !kpair.π₂.dfn p = !allCodeFormula φ ∧
      ∀ x ∈ !structureDomainFormula (!satStructureFormula P),
        !assignmentPrependFormula (!kpair.π₁.dfn p) b x ∈
          !value.dfn previous (!kpair.dfn (!succ.dfn (!kpair.π₁.dfn p)) φ)) ∨
    ∃ φ, !kpair.π₂.dfn p = !existsCodeFormula φ ∧
      ∃ x ∈ !structureDomainFormula (!satStructureFormula P),
        !assignmentPrependFormula (!kpair.π₁.dfn p) b x ∈
          !value.dfn previous (!kpair.dfn (!succ.dfn (!kpair.π₁.dfn p)) φ)”

def isPackedSatisfactionGraphFormula : SetTheorySemisentence 2 :=
  f“P g. !IsFunction.dfn g ∧ !domain.dfn g = !formulaFamilyFormula (!satLanguageFormula P) (!satVariablesFormula P) ∧
    ∀ p ∈ !formulaFamilyFormula (!satLanguageFormula P) (!satVariablesFormula P), ∀ b,
      b ∈ !value.dfn g p ↔
        b ∈ !function.dfn (!structureDomainFormula (!satStructureFormula P)) (!kpair.π₁.dfn p) ∧
        !packedSatisfactionStepHoldsFormula P p
          (!restrict.dfn g (!predecessorsFormula
            (!subformulaRelationFormula (!formulaFamilyFormula (!satLanguageFormula P) (!satVariablesFormula P)))
            (!formulaFamilyFormula (!satLanguageFormula P) (!satVariablesFormula P)) p)) b”

def packedSatisfactionGraphFormula : SetTheorySemisentence 2 :=
  f“g P. !isPackedSatisfactionGraphFormula P g”

def satisfactionGraphFormula : SetTheorySemisentence 5 :=
  f“g L Γ M e. g = !packedSatisfactionGraphFormula (!satisfactionParametersFormula L Γ M e)”

def satisfiesFormula : SetTheorySemisentence 7 :=
  f“L Γ M e n φ b. b ∈ !value.dfn (!satisfactionGraphFormula L Γ M e) (!kpair.dfn n φ)”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

instance packedEvaluatedArgumentsFormula_defined :
    ℒₛₑₜ-function₃[V] packedEvaluatedArguments via packedEvaluatedArgumentsFormula :=
  ⟨fun v ↦ by simp [packedEvaluatedArgumentsFormula, packedEvaluatedArguments]⟩

instance packedAtomicHoldsFormula_defined : ℒₛₑₜ-relation₃[V] PackedAtomicHolds via packedAtomicHoldsFormula :=
  ⟨fun v ↦ by simp [packedAtomicHoldsFormula, PackedAtomicHolds, equalityToken]⟩

instance packedSatisfactionStepHoldsFormula_defined :
    ℒₛₑₜ-relation₄[V] PackedSatisfactionStepHolds via packedSatisfactionStepHoldsFormula :=
  ⟨fun v ↦ by simp [packedSatisfactionStepHoldsFormula, PackedSatisfactionStepHolds]⟩

instance isPackedSatisfactionGraphFormula_defined :
    ℒₛₑₜ-relation[V] IsPackedSatisfactionGraph via isPackedSatisfactionGraphFormula :=
  ⟨fun v ↦ by simp [isPackedSatisfactionGraphFormula, IsPackedSatisfactionGraph]⟩

instance packedSatisfactionGraphFormula_defined :
    ℒₛₑₜ-function₁[V] packedSatisfactionGraph via packedSatisfactionGraphFormula :=
  ⟨fun v ↦ by
    change packedSatisfactionGraphFormula.Evalb v ↔ v 0 = packedSatisfactionGraph (v 1)
    rw [eq_comm]
    unfold packedSatisfactionGraph
    rw [satisfactionGraph_eq_iff]
    simp [packedSatisfactionGraphFormula, isPackedSatisfactionGraph_iff]⟩

instance satisfactionGraphFormula_defined : ℒₛₑₜ-function₄[V] satisfactionGraph via satisfactionGraphFormula :=
  ⟨fun v ↦ by simp [satisfactionGraphFormula, packedSatisfactionGraph, satisfactionParameters,
    satLanguage, satVariables, satStructure, satFreeAssignment]⟩

instance satisfiesFormula_defined : Defined
    (fun v : Fin 7 → V ↦ Satisfies (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6)) satisfiesFormula :=
  ⟨fun v ↦ by simp [satisfiesFormula, Satisfies]⟩

end ZFVP
