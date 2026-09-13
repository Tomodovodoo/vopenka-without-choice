import ZFVP.ModelTheory.WoodinInverseUniform
import ZFVP.ModelTheory.WoodinIterationRecursion

set_option maxRecDepth 4096

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

@[irreducible] def woodinStageRuleFormula : SetTheorySemisentence 4 :=
  f“z θ s K. (θ = !isEmpty ∧ z = !kpair.dfn (!woodinInitialCodeFormula) (!woodinInitialCardinalsFormula)) ∨
    (θ ≠ !isEmpty ∧ θ = !succ.dfn (!sUnion.dfn θ) ∧
      z = !kpair.dfn (!woodinIterationSuccessorFormula (!sUnion.dfn θ) s K)
        (!woodinIterationCardinalNextFormula (!sUnion.dfn θ) s K)) ∨
    (θ ≠ !isEmpty ∧ θ ≠ !succ.dfn (!sUnion.dfn θ) ∧ !choicelessInaccessibleFormula (!woodinLimitCardinalFormula K) ∧
      z = !kpair.dfn (!forcingDirectCodeFormula θ s) (!forcingFamilyNextFormula θ K (!woodinLimitCardinalFormula K))) ∨
    (θ ≠ !isEmpty ∧ θ ≠ !succ.dfn (!sUnion.dfn θ) ∧ ¬!choicelessInaccessibleFormula (!woodinLimitCardinalFormula K) ∧
      z = !kpair.dfn (!woodinInverseSourceCodeFormula θ s K) (!woodinInverseCardinalNextFormula θ s K))”

@[irreducible] def woodinHistoryCodesFormula : SetTheorySemisentence 2 :=
  f“z H. ∀ a, a ∈ z ↔ ∃ i ∈ !domain.dfn H, a = !kpair.dfn i (!kpair.π₁.dfn (!value.dfn H i))”

@[irreducible] def woodinHistoryCardinalsFormula : SetTheorySemisentence 2 :=
  f“z H. ∀ a, a ∈ z ↔ ∃ i ∈ !domain.dfn H, a = !kpair.dfn i (!kpair.π₂.dfn (!value.dfn H i))”

@[irreducible] def woodinHistoryCardinalUnionFormula : SetTheorySemisentence 3 :=
  f“z θ J. ∀ a, a ∈ z ↔ ∃ i ∈ θ, a ∈ !value.dfn J i”

@[irreducible] def woodinIterationRecursionStepFormula : SetTheorySemisentence 2 :=
  f“z H. !woodinStageRuleFormula z (!domain.dfn H)
    (!forcingIterationCodeUnionFormula (!domain.dfn H) (!woodinHistoryCodesFormula H))
    (!woodinHistoryCardinalUnionFormula (!domain.dfn H) (!woodinHistoryCardinalsFormula H))”

@[irreducible] def woodinIterationRecFormula : SetTheorySemisentence 2 :=
  transfiniteRecFormula woodinIterationRecursionStepFormula

@[irreducible] def woodinIterationHistoryFormula : SetTheorySemisentence 2 :=
  f“z θ. ∀ a, a ∈ z ↔ ∃ i ∈ θ, a = !kpair.dfn i (!woodinIterationRecFormula i)”

@[irreducible] def woodinIterationPrefixFormula : SetTheorySemisentence 2 :=
  f“z θ. !forcingIterationCodeUnionFormula z θ (!woodinHistoryCodesFormula (!woodinIterationHistoryFormula θ))”

@[irreducible] def woodinIterationCardinalPrefixFormula : SetTheorySemisentence 2 :=
  f“z θ. !woodinHistoryCardinalUnionFormula z θ (!woodinHistoryCardinalsFormula (!woodinIterationHistoryFormula θ))”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

instance woodinStageRuleFormula_defined : ℒₛₑₜ-function₃[V] woodinStageRule via woodinStageRuleFormula := by
  refine ⟨fun v ↦ ?_⟩
  classical
  simp [woodinStageRuleFormula]
  simp only [← not_isEmpty_iff_isNonempty, isEmpty_iff_eq_empty]
  unfold woodinStageRule
  split_ifs <;> tauto

instance woodinHistoryCodesFormula_defined : ℒₛₑₜ-function₁[V] woodinHistoryCodes via woodinHistoryCodesFormula :=
  ⟨fun v ↦ by rw [mem_ext_iff]; simp [woodinHistoryCodesFormula, woodinHistoryCodes, mem_definableGraph_iff]⟩

instance woodinHistoryCardinalsFormula_defined : ℒₛₑₜ-function₁[V] woodinHistoryCardinals via woodinHistoryCardinalsFormula :=
  ⟨fun v ↦ by rw [mem_ext_iff]; simp [woodinHistoryCardinalsFormula, woodinHistoryCardinals, mem_definableGraph_iff]⟩

instance woodinHistoryCardinalUnionFormula_defined :
    ℒₛₑₜ-function₂[V] woodinHistoryCardinalUnion via woodinHistoryCardinalUnionFormula :=
  ⟨fun v ↦ by
    rw [mem_ext_iff]
    simp [woodinHistoryCardinalUnionFormula, woodinHistoryCardinalUnion, iterationTableUnion, mem_sUnion_iff, repl_spec]⟩

instance woodinIterationRecursionStepFormula_defined :
    ℒₛₑₜ-function₁[V] woodinIterationRecursionStep via woodinIterationRecursionStepFormula :=
  ⟨fun v ↦ by simp [woodinIterationRecursionStepFormula, woodinIterationRecursionStep]⟩

instance woodinIterationRecFormula_defined : ℒₛₑₜ-function₁[V] woodinIterationRec via woodinIterationRecFormula := by
  unfold woodinIterationRecFormula woodinIterationRec
  exact transfiniteRecFormula_defined woodinIterationRecursionStep woodinIterationRecursionStepFormula

instance woodinIterationHistoryFormula_defined :
    ℒₛₑₜ-function₁[V] woodinIterationHistory via woodinIterationHistoryFormula :=
  ⟨fun v ↦ by rw [mem_ext_iff]; simp [woodinIterationHistoryFormula, woodinIterationHistory, mem_definableGraph_iff]⟩

instance woodinIterationPrefixFormula_defined :
    ℒₛₑₜ-function₁[V] woodinIterationPrefix via woodinIterationPrefixFormula :=
  ⟨fun v ↦ by simp [woodinIterationPrefixFormula, woodinIterationPrefix]⟩

instance woodinIterationCardinalPrefixFormula_defined :
    ℒₛₑₜ-function₁[V] woodinIterationCardinalPrefix via woodinIterationCardinalPrefixFormula :=
  ⟨fun v ↦ by simp [woodinIterationCardinalPrefixFormula, woodinIterationCardinalPrefix]⟩

end ZFVP
