import ZFVP.ModelTheory.ForcingInvariantUniform
import ZFVP.ModelTheory.WoodinRecursionUniform
import ZFVP.ModelTheory.WoodinIterationContract

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

@[irreducible] def isWoodinStageFormula : SetTheorySemisentence 1 :=
  f“x. !forcingPreorderFormula (!woodinStagePosetFormula x) (!woodinStageOrderFormula x) ∧
    !forcingTopFormula (!woodinStagePosetFormula x) (!woodinStageOrderFormula x) (!woodinStageTopFormula x) ∧
    !IsOrdinal.dfn (!woodinStageCardinalValueFormula x) ∧
    (∀ p ∈ !woodinStagePosetFormula x, !(checkedUnaryForcingFormula regularCardinalFormula)
      (!woodinStagePosetFormula x) (!woodinStageOrderFormula x) (!woodinStageTopFormula x) p (!woodinStageCardinalValueFormula x)) ∧
    (∀ p ∈ !woodinStagePosetFormula x, !(checkedUnaryForcingFormula dependentChoiceBelowFormula)
      (!woodinStagePosetFormula x) (!woodinStageOrderFormula x) (!woodinStageTopFormula x) p (!woodinStageCardinalValueFormula x))”

@[irreducible] def isWoodinStageSmallFormula : SetTheorySemisentence 1 :=
  f“x. ∀ θ, !choicelessInaccessibleFormula θ → !woodinStageCardinalValueFormula x ∈ θ →
    !woodinStagePosetFormula x ∈ !hierarchyFormula θ”

@[irreducible] def isWoodinIterationFormula : SetTheorySemisentence 4 :=
  f“δ θ s K. !isForcingIterationCodeFormula θ s ∧ !iterationTableFormula θ K ∧
    (∀ i ∈ θ, !isWoodinStageFormula (!woodinIterationStageFormula s K i)) ∧
    (∀ i ∈ θ, !isWoodinStageSmallFormula (!woodinIterationStageFormula s K i)) ∧
    (∀ i ∈ θ, !choicelessInaccessibleFormula (!value.dfn K i)) ∧
    (∀ i ∈ θ, !value.dfn K i ∈ δ) ∧
    (∀ i ∈ θ, ∀ j ∈ θ, i ∈ j → !value.dfn K i ∈ !value.dfn K j)”

@[irreducible] def iterationQuotientClosedBelowFormula : SetTheorySemisentence 4 :=
  f“s i j η. !allProjectionQuotientClosedBelowFormula (!value.dfn (!forcingCodePFormula s) i)
    (!value.dfn (!forcingCodeRFormula s) i) (!value.dfn (!forcingCodetFormula s) i)
    (!value.dfn (!forcingCodePFormula s) j) (!value.dfn (!forcingCodeRFormula s) j)
    (!value.dfn (!forcingCodeπFormula s) (!kpair.dfn i j)) η”

@[irreducible] def hasWoodinQuotientClosureFormula : SetTheorySemisentence 3 :=
  f“θ s K. ∀ i ∈ θ, ∀ j ∈ θ, i ⊆ j → !iterationQuotientClosedBelowFormula s i j (!value.dfn K i)”

@[irreducible] def leastDependentChoiceFailureFormula : SetTheorySemisentence 1 :=
  f“κ. !IsOrdinal.dfn κ ∧ ¬!dependentChoiceAtFormula κ ∧
    ∀ γ, !IsOrdinal.dfn γ → ¬!dependentChoiceAtFormula γ → κ ⊆ γ”

@[irreducible] def woodinRecursiveStageValidFormula : SetTheorySemisentence 2 :=
  f“δ θ. ∀ z, !woodinIterationRecFormula z θ →
    !isWoodinIterationFormula δ (!succ.dfn θ) (!kpair.π₁.dfn z) (!kpair.π₂.dfn z) ∧
    !hasWoodinQuotientClosureFormula (!succ.dfn θ) (!kpair.π₁.dfn z) (!kpair.π₂.dfn z)”

@[irreducible] def woodinIterationExitFormula : SetTheorySemisentence 1 :=
  f“δ. !leastDependentChoiceFailureFormula (!woodinSeedCardinalFormula) ∧
    (∀ θ ∈ δ, !woodinRecursiveStageValidFormula δ θ) ∧
    !isWoodinIterationFormula δ δ (!woodinIterationPrefixFormula δ) (!woodinIterationCardinalPrefixFormula δ) ∧
    !hasWoodinQuotientClosureFormula δ (!woodinIterationPrefixFormula δ) (!woodinIterationCardinalPrefixFormula δ)”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

instance isWoodinStageFormula_defined : ℒₛₑₜ-predicate[V] IsWoodinStage via isWoodinStageFormula :=
  ⟨fun v ↦ by simp [isWoodinStageFormula, IsWoodinStage]⟩

instance isWoodinStageSmallFormula_defined : ℒₛₑₜ-predicate[V] IsWoodinStageSmall via isWoodinStageSmallFormula :=
  ⟨fun v ↦ by simp [isWoodinStageSmallFormula, IsWoodinStageSmall]⟩

instance isWoodinIterationFormula_defined : ℒₛₑₜ-relation₄[V] IsWoodinIteration via isWoodinIterationFormula := by
  refine ⟨fun v ↦ ?_⟩
  simp [isWoodinIterationFormula]
  exact ⟨fun h ↦ ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩,
    fun h ↦ ⟨h.code, h.cardinals, h.stage, h.small, h.inaccessible, h.bounded, h.increasing⟩⟩

instance iterationQuotientClosedBelowFormula_defined :
    ℒₛₑₜ-relation₄[V] IterationQuotientClosedBelow via iterationQuotientClosedBelowFormula :=
  ⟨fun v ↦ by simp [iterationQuotientClosedBelowFormula, IterationQuotientClosedBelow]⟩

instance hasWoodinQuotientClosureFormula_defined :
    ℒₛₑₜ-relation₃[V] HasWoodinQuotientClosure via hasWoodinQuotientClosureFormula :=
  ⟨fun v ↦ by simp [hasWoodinQuotientClosureFormula, HasWoodinQuotientClosure]⟩

instance leastDependentChoiceFailureFormula_defined :
    ℒₛₑₜ-predicate[V] IsLeastDependentChoiceFailure via leastDependentChoiceFailureFormula :=
  ⟨fun v ↦ by simp [leastDependentChoiceFailureFormula, IsLeastDependentChoiceFailure, IsLeastOrdinal]⟩

instance woodinRecursiveStageValidFormula_defined : Defined
    (fun v : Fin 2 → V ↦ IsWoodinIteration (v 0) (succ (v 1)) (kpair.π₁ (woodinIterationRec (v 1)))
      (kpair.π₂ (woodinIterationRec (v 1))) ∧ HasWoodinQuotientClosure (succ (v 1))
      (kpair.π₁ (woodinIterationRec (v 1))) (kpair.π₂ (woodinIterationRec (v 1)))) woodinRecursiveStageValidFormula :=
  ⟨fun v ↦ by simp [woodinRecursiveStageValidFormula]⟩

instance woodinIterationExitFormula_defined : ℒₛₑₜ-predicate[V] WoodinIterationExit via woodinIterationExitFormula :=
  ⟨fun v ↦ by simp [woodinIterationExitFormula, WoodinIterationExit]⟩

end ZFVP
