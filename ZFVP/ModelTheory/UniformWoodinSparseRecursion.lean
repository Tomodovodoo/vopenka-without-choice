import ZFVP.ModelTheory.UniformWoodinSparseMaps
import ZFVP.ModelTheory.UniformForcingRecodedCode
import ZFVP.ModelTheory.WoodinSparseStageCode

/-! One fixed formula for the actual sparse recursion, history and stage code.
Its ingredients are explicit syntax, independent of the interpreted ZF model. -/

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

def woodinRecodingCarriersFormula : SetTheorySemisentence 2 :=
  f“Q H. ∀ z, z ∈ Q ↔ ∃ i ∈ !domain.dfn H,
    z = !kpair.dfn i (!kpair.π₁.dfn (!value.dfn H i))”

def woodinRecodingOrdersFormula : SetTheorySemisentence 2 :=
  f“T H. ∀ z, z ∈ T ↔ ∃ i ∈ !domain.dfn H,
    z = !kpair.dfn i (!kpair.π₁.dfn (!kpair.π₂.dfn (!value.dfn H i)))”

def woodinRecodingMapsFormula : SetTheorySemisentence 2 :=
  f“m H. ∀ z, z ∈ m ↔ ∃ i ∈ !domain.dfn H,
    z = !kpair.dfn i (!kpair.π₂.dfn (!kpair.π₂.dfn (!value.dfn H i)))”

def woodinSparseRecodingInitialRowFormula : SetTheorySemisentence 1 :=
  “z. ∃ Q, ∃ T, ∃ m, ∃ u, !woodinSparseInitialCarrierFormula Q ∧
    !woodinSparseInitialOrderFormula T ∧ !woodinSparseInitialMapFormula m ∧
    !kpair.dfn u T m ∧ !kpair.dfn z Q u”

def woodinSparseRecodingSuccessorRowFormula : SetTheorySemisentence 4 :=
  “z k c m. ∃ Q, ∃ T, ∃ f, ∃ u, !woodinSparseSuccessorCarrierFormula Q k c ∧
    !woodinSparseSuccessorOrderFormula T k c ∧ !woodinSparseSuccessorMapFormula f k c m ∧
    !kpair.dfn u T f ∧ !kpair.dfn z Q u”

def woodinSparseRecodingDirectRowFormula : SetTheorySemisentence 4 :=
  “z θ c m. ∃ Q, ∃ T, ∃ f, ∃ u, !woodinSparseDirectBaseFormula Q θ c ∧
    !woodinSparseDirectOrderFormula T θ c ∧ !woodinSparseDirectMapFormula f θ c m ∧
    !kpair.dfn u T f ∧ !kpair.dfn z Q u”

def woodinSparseRecodingInverseRowFormula : SetTheorySemisentence 4 :=
  “z θ c m. ∃ Q, ∃ T, ∃ f, ∃ u, !woodinSparseCompletedInverseCarrierFormula Q θ c ∧
    !woodinSparseCompletedInverseOrderFormula T θ c ∧ !woodinSparseCompletedInverseMapFormula f θ c m ∧
    !kpair.dfn u T f ∧ !kpair.dfn z Q u”

def woodinSparseRecodingRowRuleFormula : SetTheorySemisentence 4 :=
  f“z θ c m.
    (θ = !isEmpty ∧ !woodinSparseRecodingInitialRowFormula z) ∨
    (θ ≠ !isEmpty ∧ θ = !succ.dfn (!sUnion.dfn θ) ∧
      !woodinSparseRecodingSuccessorRowFormula z (!sUnion.dfn θ) c m) ∨
    (θ ≠ !isEmpty ∧ θ ≠ !succ.dfn (!sUnion.dfn θ) ∧
      !choicelessInaccessibleFormula (!woodinLimitCardinalFormula (!woodinIterationCardinalPrefixFormula θ)) ∧
      !woodinSparseRecodingDirectRowFormula z θ c m) ∨
    (θ ≠ !isEmpty ∧ θ ≠ !succ.dfn (!sUnion.dfn θ) ∧
      ¬!choicelessInaccessibleFormula (!woodinLimitCardinalFormula (!woodinIterationCardinalPrefixFormula θ)) ∧
      !woodinSparseRecodingInverseRowFormula z θ c m)”

def woodinSparseRecodingRuleFormula : SetTheorySemisentence 5 :=
  “z θ Q T m. ∃ N, ∃ c, !woodinNormalizedPrefixCodeFormula N θ ∧
    !forcingRecodedCodeFormula c θ N Q T m ∧ !woodinSparseRecodingRowRuleFormula z θ c m”

def woodinSparseRecodingStepFormula : SetTheorySemisentence 2 :=
  “z H. ∃ θ, ∃ Q, ∃ T, ∃ m, !domain.dfn θ H ∧ !woodinRecodingCarriersFormula Q H ∧
    !woodinRecodingOrdersFormula T H ∧ !woodinRecodingMapsFormula m H ∧
    !woodinSparseRecodingRuleFormula z θ Q T m”

def woodinSparseRecodingRecFormula : SetTheorySemisentence 2 :=
  transfiniteRecFormula woodinSparseRecodingStepFormula

def woodinSparseRecodingHistoryFormula : SetTheorySemisentence 2 :=
  f“H θ. ∀ z, z ∈ H ↔ ∃ i ∈ θ, z = !kpair.dfn i (!woodinSparseRecodingRecFormula i)”

def woodinSparsePrefixCodeFormula : SetTheorySemisentence 2 :=
  “c θ. ∃ H, ∃ N, ∃ Q, ∃ T, ∃ m, !woodinSparseRecodingHistoryFormula H θ ∧
    !woodinNormalizedPrefixCodeFormula N θ ∧ !woodinRecodingCarriersFormula Q H ∧
    !woodinRecodingOrdersFormula T H ∧ !woodinRecodingMapsFormula m H ∧
    !forcingRecodedCodeFormula c θ N Q T m”

def woodinSparseStageCodeFormula : SetTheorySemisentence 2 :=
  “c θ. ∃ η, ∃ H, ∃ N, ∃ Q, ∃ T, ∃ m, !succ.dfn η θ ∧
    !woodinSparseRecodingHistoryFormula H η ∧ !woodinNormalizedStageCodeFormula N θ ∧
    !woodinRecodingCarriersFormula Q H ∧ !woodinRecodingOrdersFormula T H ∧
    !woodinRecodingMapsFormula m H ∧ !forcingRecodedCodeFormula c η N Q T m”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

instance woodinRecodingCarriersFormula_defined :
    ℒₛₑₜ-function₁[V] woodinRecodingCarriers via woodinRecodingCarriersFormula :=
  ⟨fun v ↦ by rw [mem_ext_iff]; simp [woodinRecodingCarriersFormula, woodinRecodingCarriers, mem_definableGraph_iff]⟩

instance woodinRecodingOrdersFormula_defined :
    ℒₛₑₜ-function₁[V] woodinRecodingOrders via woodinRecodingOrdersFormula :=
  ⟨fun v ↦ by rw [mem_ext_iff]; simp [woodinRecodingOrdersFormula, woodinRecodingOrders, mem_definableGraph_iff]⟩

instance woodinRecodingMapsFormula_defined :
    ℒₛₑₜ-function₁[V] woodinRecodingMaps via woodinRecodingMapsFormula :=
  ⟨fun v ↦ by rw [mem_ext_iff]; simp [woodinRecodingMapsFormula, woodinRecodingMaps, mem_definableGraph_iff]⟩

instance woodinSparseRecodingInitialRowFormula_defined :
    ℒₛₑₜ-function₀[V] woodinSparseRecodingInitialRow via woodinSparseRecodingInitialRowFormula :=
  ⟨fun v ↦ by simp [woodinSparseRecodingInitialRowFormula, woodinSparseRecodingInitialRow]⟩

instance woodinSparseRecodingSuccessorRowFormula_defined :
    ℒₛₑₜ-function₃[V] woodinSparseRecodingSuccessorRow via woodinSparseRecodingSuccessorRowFormula :=
  ⟨fun v ↦ by simp [woodinSparseRecodingSuccessorRowFormula, woodinSparseRecodingSuccessorRow]⟩

instance woodinSparseRecodingDirectRowFormula_defined :
    ℒₛₑₜ-function₃[V] woodinSparseRecodingDirectRow via woodinSparseRecodingDirectRowFormula :=
  ⟨fun v ↦ by simp [woodinSparseRecodingDirectRowFormula, woodinSparseRecodingDirectRow]⟩

instance woodinSparseRecodingInverseRowFormula_defined :
    ℒₛₑₜ-function₃[V] woodinSparseRecodingInverseRow via woodinSparseRecodingInverseRowFormula :=
  ⟨fun v ↦ by simp [woodinSparseRecodingInverseRowFormula, woodinSparseRecodingInverseRow]⟩

instance woodinSparseRecodingRowRuleFormula_defined :
    ℒₛₑₜ-function₃[V] woodinSparseRecodingRowRule via woodinSparseRecodingRowRuleFormula := by
  refine ⟨fun v ↦ ?_⟩
  classical
  simp [woodinSparseRecodingRowRuleFormula]
  simp only [← not_isEmpty_iff_isNonempty, isEmpty_iff_eq_empty]
  unfold woodinSparseRecodingRowRule
  split_ifs <;> tauto

instance woodinSparseRecodingRuleFormula_defined :
    ℒₛₑₜ-function₄[V] woodinSparseRecodingRule via woodinSparseRecodingRuleFormula :=
  ⟨fun v ↦ by simp [woodinSparseRecodingRuleFormula, woodinSparseRecodingRule]⟩

instance woodinSparseRecodingStepFormula_defined :
    ℒₛₑₜ-function₁[V] woodinSparseRecodingStep via woodinSparseRecodingStepFormula :=
  ⟨fun v ↦ by simp [woodinSparseRecodingStepFormula, woodinSparseRecodingStep]⟩

instance woodinSparseRecodingRecFormula_defined :
    ℒₛₑₜ-function₁[V] woodinSparseRecodingRec via woodinSparseRecodingRecFormula := by
  unfold woodinSparseRecodingRecFormula woodinSparseRecodingRec
  exact transfiniteRecFormula_defined woodinSparseRecodingStep woodinSparseRecodingStepFormula

instance woodinSparseRecodingHistoryFormula_defined :
    ℒₛₑₜ-function₁[V] woodinSparseRecodingHistory via woodinSparseRecodingHistoryFormula :=
  ⟨fun v ↦ by rw [mem_ext_iff]; simp [woodinSparseRecodingHistoryFormula,
    woodinSparseRecodingHistory, mem_definableGraph_iff]⟩

instance woodinSparsePrefixCodeFormula_defined :
    ℒₛₑₜ-function₁[V] woodinSparsePrefixCode via woodinSparsePrefixCodeFormula :=
  ⟨fun v ↦ by simp [woodinSparsePrefixCodeFormula, woodinSparsePrefixCode]⟩

instance woodinSparseStageCodeFormula_defined :
    ℒₛₑₜ-function₁[V] woodinSparseStageCode via woodinSparseStageCodeFormula :=
  ⟨fun v ↦ by simp [woodinSparseStageCodeFormula, woodinSparseStageCode]⟩

theorem eval_woodinSparseStageCodeFormula (c θ : V) :
    woodinSparseStageCodeFormula.Evalb ![c, θ] ↔ c = woodinSparseStageCode θ :=
  Defined.eval_iff (φ := woodinSparseStageCodeFormula) ![c, θ]

def woodinSparseRecursionDictionary : SetFormulaDictionary :=
  [⟨2, woodinRecodingCarriersFormula⟩, ⟨2, woodinRecodingOrdersFormula⟩,
   ⟨2, woodinRecodingMapsFormula⟩, ⟨1, woodinSparseRecodingInitialRowFormula⟩,
   ⟨4, woodinSparseRecodingSuccessorRowFormula⟩, ⟨4, woodinSparseRecodingDirectRowFormula⟩,
   ⟨4, woodinSparseRecodingInverseRowFormula⟩, ⟨4, woodinSparseRecodingRowRuleFormula⟩,
   ⟨5, woodinSparseRecodingRuleFormula⟩, ⟨2, woodinSparseRecodingStepFormula⟩,
   ⟨2, woodinSparseRecodingRecFormula⟩, ⟨2, woodinSparseRecodingHistoryFormula⟩,
   ⟨2, woodinSparsePrefixCodeFormula⟩, ⟨2, woodinSparseStageCodeFormula⟩]

def woodinSparseRecursionDictionaryBound : ℕ := levyDictionaryBound woodinSparseRecursionDictionary

theorem woodinSparseRecursionDictionary_complexity {n : ℕ} {φ : SetTheorySemisentence n}
    (hφ : ⟨n, φ⟩ ∈ woodinSparseRecursionDictionary) (p : LevyPolarity) :
    IsLevyFormula p woodinSparseRecursionDictionaryBound φ :=
  isLevyFormula_dictionaryBound _ hφ p

end ZFVP
