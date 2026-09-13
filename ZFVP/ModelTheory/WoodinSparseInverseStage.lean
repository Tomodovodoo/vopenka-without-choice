import ZFVP.ModelTheory.WoodinSparseInverseTransport
import ZFVP.ModelTheory.WoodinNormalizedInverseCutoff
import ZFVP.ModelTheory.NormalizedHartogsIsomorphism
import ZFVP.ModelTheory.SparseNormalizedTwoStep

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def woodinSparseInverseCutoff (θ c : V) : V :=
  let A := woodinSparseInverseBase θ c
  let B := woodinSparseInverseOrder θ c
  let γ := woodinLimitCardinal (woodinIterationCardinalPrefix θ)
  woodinNamedPrefixCutoff A B ∅ γ (hartogsNumberName A B (checkName ∅ γ))

noncomputable def woodinSparseInversePool (θ c : V) : V :=
  let A := woodinSparseInverseBase θ c
  let B := woodinSparseInverseOrder θ c
  let γ := woodinLimitCardinal (woodinIterationCardinalPrefix θ)
  let δ := woodinSparseInverseCutoff θ c
  normalizedNamePool A B ∅ δ (saturatedHartogsPosetName A B ∅ γ δ)

noncomputable def woodinSparseCompletedInverseCarrier (θ c : V) : V :=
  sparsePairCarrier θ (woodinSparseInverseBase θ c) (woodinSparseInversePool θ c)

noncomputable def woodinSparseInversePairCarrier (θ c : V) : V :=
  (woodinSparseInverseBase θ c) ×ˢ (woodinSparseInversePool θ c)

noncomputable def woodinSparseInversePairOrder (θ c : V) : V :=
  let A := woodinSparseInverseBase θ c
  let B := woodinSparseInverseOrder θ c
  let γ := woodinLimitCardinal (woodinIterationCardinalPrefix θ)
  nameTwoStepOrderOn A B (saturatedHartogsOrderName A B ∅ γ (woodinSparseInverseCutoff θ c))
    (woodinSparseInversePairCarrier θ c)

noncomputable def woodinSparseCompletedInverseOrder (θ c : V) : V :=
  forcingPullbackOrder (woodinSparseCompletedInverseCarrier θ c) (woodinSparseInversePairOrder θ c)
    (sparsePairDecode θ (woodinSparseInverseBase θ c) (woodinSparseInversePool θ c))

noncomputable def woodinSparseInversePairMap (θ c m : V) : V :=
  let P := woodinNormalizedInverseBase θ
  let R := woodinNormalizedInverseOrder θ
  let one := forcingInverseCodeTop θ (woodinIterationPrefix θ)
  let δ := woodinNormalizedInverseCutoff θ
  let γ := woodinLimitCardinal (woodinIterationCardinalPrefix θ)
  normalizedTwoStepIsoMap P R one δ (saturatedHartogsPosetName P R one γ δ)
    (woodinSparseInverseBase θ c) (woodinSparseInverseOrder θ c) ∅ (woodinSparseInverseBaseMap θ c m)

noncomputable def woodinSparseCompletedInverseMap (θ c m : V) : V :=
  compose (woodinSparseInversePairMap θ c m)
    (sparsePairEncode θ (woodinSparseInverseBase θ c) (woodinSparseInversePool θ c))

attribute [local aesop 5 (rule_sets := [Definability]) safe]
  Language.DefinableFunction₄.comp Language.DefinableFunction₅.comp

instance woodinSparseInverseCutoff_definable : ℒₛₑₜ-function₂[V] woodinSparseInverseCutoff := by
  unfold woodinSparseInverseCutoff
  dsimp only
  apply Language.DefinableFunction₅.comp <;> definability

instance woodinSparseInversePool_definable : ℒₛₑₜ-function₂[V] woodinSparseInversePool := by
  unfold woodinSparseInversePool
  dsimp only
  apply Language.DefinableFunction₅.comp <;> definability

instance woodinSparseCompletedInverseCarrier_definable : ℒₛₑₜ-function₂[V] woodinSparseCompletedInverseCarrier := by
  unfold woodinSparseCompletedInverseCarrier
  apply Language.DefinableFunction₃.comp <;> definability

instance woodinSparseInversePairCarrier_definable : ℒₛₑₜ-function₂[V] woodinSparseInversePairCarrier := by
  unfold woodinSparseInversePairCarrier
  definability

instance woodinSparseInversePairOrder_definable : ℒₛₑₜ-function₂[V] woodinSparseInversePairOrder := by
  unfold woodinSparseInversePairOrder
  dsimp only
  apply Language.DefinableFunction₄.comp <;> definability

instance woodinSparseCompletedInverseOrder_definable : ℒₛₑₜ-function₂[V] woodinSparseCompletedInverseOrder := by
  unfold woodinSparseCompletedInverseOrder
  apply Language.DefinableFunction₃.comp <;> definability

instance woodinSparseInversePairMap_definable : ℒₛₑₜ-function₃[V] woodinSparseInversePairMap := by
  unfold woodinSparseInversePairMap
  dsimp only
  apply normalizedTwoStepIsoMap_comp <;> definability

instance woodinSparseCompletedInverseMap_definable : ℒₛₑₜ-function₃[V] woodinSparseCompletedInverseMap := by
  unfold woodinSparseCompletedInverseMap
  apply Language.DefinableFunction₂.comp
  · apply Language.DefinableFunction₃.comp (F := woodinSparseInversePairMap) <;> definability
  · apply Language.DefinableFunction₃.comp (F := sparsePairEncode) <;> definability

theorem woodinSparseInverseEncode_isomorphism {θ c : V} :
    IsForcingIsomorphism (woodinSparseInversePairCarrier θ c) (woodinSparseInversePairOrder θ c)
      (woodinSparseCompletedInverseCarrier θ c) (woodinSparseCompletedInverseOrder θ c)
      (sparsePairEncode θ (woodinSparseInverseBase θ c) (woodinSparseInversePool θ c)) := by
  apply sparsePairEncode_isomorphism
  intro p hp
  exact sparseThreadCarrier_isSparse hp

theorem mem_woodinSparseCompletedInverseCarrier_iff {θ c q : V} :
    q ∈ woodinSparseCompletedInverseCarrier θ c ↔ IsSparseFunctionOn (succ θ) q ∧
      q ↾ θ ∈ woodinSparseInverseBase θ c ∧ q ‘ θ ∈ woodinSparseInversePool θ c := mem_sparsePairCarrier_iff

end ZFVP
