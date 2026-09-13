import ZFVP.ModelTheory.WoodinRecodedSuccessorValues
import ZFVP.ModelTheory.SparseNormalizedTwoStep
import ZFVP.SetTheory.WoodinSourceIndex

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def woodinSparseSuccessorPool (k c : V) : V :=
  let P := (forcingCodeP c) ‘ k
  let R := (forcingCodeR c) ‘ k
  let o := (forcingCodet c) ‘ k
  let κ := (kpair.π₂ (woodinIterationRec k)) ‘ k
  let δ := woodinPrefixCutoff P R o κ
  normalizedNamePool P R o δ (saturatedWoodinPrefixPosetName P R o κ δ)

noncomputable def woodinSparseSuccessorCarrier (k c : V) : V :=
  sparsePairCarrier (woodinSourceIndex (succ k)) ((forcingCodeP c) ‘ k) (woodinSparseSuccessorPool k c)

noncomputable def woodinSparseSuccessorOrder (k c : V) : V :=
  forcingPullbackOrder (woodinSparseSuccessorCarrier k c) (woodinRecodedSuccessorOrder k c)
    (sparsePairDecode (woodinSourceIndex (succ k)) ((forcingCodeP c) ‘ k) (woodinSparseSuccessorPool k c))

noncomputable def woodinSparseSuccessorMap (k c m : V) : V :=
  compose (woodinRecodedSuccessorMap k c m)
    (sparsePairEncode (woodinSourceIndex (succ k)) ((forcingCodeP c) ‘ k) (woodinSparseSuccessorPool k c))

attribute [local aesop 5 (rule_sets := [Definability]) safe]
  Language.DefinableFunction₄.comp Language.DefinableFunction₅.comp

instance woodinSparseSuccessorPool_definable : ℒₛₑₜ-function₂[V] woodinSparseSuccessorPool := by
  unfold woodinSparseSuccessorPool
  dsimp only
  apply Language.DefinableFunction₅.comp <;> definability

instance woodinSparseSuccessorCarrier_definable : ℒₛₑₜ-function₂[V] woodinSparseSuccessorCarrier := by
  unfold woodinSparseSuccessorCarrier
  definability

instance woodinSparseSuccessorOrder_definable : ℒₛₑₜ-function₂[V] woodinSparseSuccessorOrder := by
  unfold woodinSparseSuccessorOrder
  definability

instance woodinSparseSuccessorMap_definable : ℒₛₑₜ-function₃[V] woodinSparseSuccessorMap := by
  unfold woodinSparseSuccessorMap
  definability

theorem mem_woodinSparseSuccessorCarrier_iff {k c q : V} :
    q ∈ woodinSparseSuccessorCarrier k c ↔
      IsSparseFunctionOn (succ (woodinSourceIndex (succ k))) q ∧
      q ↾ (woodinSourceIndex (succ k)) ∈ (forcingCodeP c) ‘ k ∧
      q ‘ (woodinSourceIndex (succ k)) ∈ woodinSparseSuccessorPool k c := mem_sparsePairCarrier_iff

theorem woodinSparseSuccessorEncode_isomorphism {k c : V}
    (hsp : ∀ p ∈ (forcingCodeP c) ‘ k, IsSparseFunctionOn (woodinSourceIndex (succ k)) p) :
    IsForcingIsomorphism (woodinRecodedSuccessorCarrier k c) (woodinRecodedSuccessorOrder k c)
      (woodinSparseSuccessorCarrier k c) (woodinSparseSuccessorOrder k c)
      (sparsePairEncode (woodinSourceIndex (succ k)) ((forcingCodeP c) ‘ k) (woodinSparseSuccessorPool k c)) :=
  sparsePairEncode_isomorphism hsp

variable {Ω k Q T m : V} [IsOrdinal k]

variable (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hk : k ∈ Ω)
variable (hm : ∀ i ∈ succ k, IsForcingIsomorphism ((forcingCodeP (woodinNormalizedPrefixCode (succ k))) ‘ i) ((forcingCodeR (woodinNormalizedPrefixCode (succ k))) ‘ i)
  (Q ‘ i) (T ‘ i) (m ‘ i))
variable (hT : ∀ i ∈ succ k, IsForcingPreorder (Q ‘ i) (T ‘ i))
variable (hQt : IsIterationTable (succ k) Q) (hTt : IsIterationTable (succ k) T)
variable (hQrank : Q ‘ k ∈ hierarchy (woodinNormalizedSuccessorCutoff k))
variable (hsp : ∀ p ∈ Q ‘ k, IsSparseFunctionOn (woodinSourceIndex (succ k)) p)

include hΩ hAC hk hm hT hQt hTt hQrank hsp

theorem woodinSparseSuccessorMap_isomorphism :
    IsForcingIsomorphism ((forcingCodeP (woodinNormalizedStageCode (succ k))) ‘ (succ k)) ((forcingCodeR (woodinNormalizedStageCode (succ k))) ‘ (succ k))
      (woodinSparseSuccessorCarrier k (forcingRecodedCode (succ k) (woodinNormalizedPrefixCode (succ k)) Q T m)) (woodinSparseSuccessorOrder k (forcingRecodedCode (succ k) (woodinNormalizedPrefixCode (succ k)) Q T m)) (woodinSparseSuccessorMap k (forcingRecodedCode (succ k) (woodinNormalizedPrefixCode (succ k)) Q T m) m) := by
  have hf := woodinRecodedSuccessorMap_isomorphism (k := k) (Q := Q) (T := T) (m := m) hΩ hAC hk hm hT hQt hTt hQrank
  change IsForcingIsomorphism _ _ (woodinRecodedSuccessorCarrier k (forcingRecodedCode (succ k) (woodinNormalizedPrefixCode (succ k)) Q T m)) (woodinRecodedSuccessorOrder k (forcingRecodedCode (succ k) (woodinNormalizedPrefixCode (succ k)) Q T m))
    (woodinRecodedSuccessorMap k (forcingRecodedCode (succ k) (woodinNormalizedPrefixCode (succ k)) Q T m) m) at hf
  have hsp' : ∀ p ∈ (forcingCodeP (forcingRecodedCode (succ k) (woodinNormalizedPrefixCode (succ k)) Q T m)) ‘ k, IsSparseFunctionOn (woodinSourceIndex (succ k)) p := by
    simpa only [forcingRecodedCode, forcingCodeP_code] using hsp
  have he := woodinSparseSuccessorEncode_isomorphism (k := k) (c := (forcingRecodedCode (succ k) (woodinNormalizedPrefixCode (succ k)) Q T m)) hsp'
  exact hf.comp he

theorem woodinSparseSuccessorMap_value {z : V} (hz : z ∈ (forcingCodeP (woodinNormalizedStageCode (succ k))) ‘ (succ k)) :
    (woodinSparseSuccessorMap k (forcingRecodedCode (succ k) (woodinNormalizedPrefixCode (succ k)) Q T m) m) ‘ z =
      sparseAppend (woodinSourceIndex (succ k))
        ((m ‘ k) ‘ (kpair.π₁ z))
        (normalizedIsomorphismName ((forcingCodeP (forcingRecodedCode (succ k) (woodinNormalizedPrefixCode (succ k)) Q T m)) ‘ k) ((forcingCodeR (forcingRecodedCode (succ k) (woodinNormalizedPrefixCode (succ k)) Q T m)) ‘ k) ((forcingCodet (forcingRecodedCode (succ k) (woodinNormalizedPrefixCode (succ k)) Q T m)) ‘ k)
          (m ‘ k) (kpair.π₂ z)) := by
  have hsp' : ∀ p ∈ (forcingCodeP (forcingRecodedCode (succ k) (woodinNormalizedPrefixCode (succ k)) Q T m)) ‘ k, IsSparseFunctionOn (woodinSourceIndex (succ k)) p := by
    simpa only [forcingRecodedCode, forcingCodeP_code] using hsp
  have hf := woodinRecodedSuccessorMap_isomorphism (k := k) (Q := Q) (T := T) (m := m) hΩ hAC hk hm hT hQt hTt hQrank
  change IsForcingIsomorphism _ _ (woodinRecodedSuccessorCarrier k (forcingRecodedCode (succ k) (woodinNormalizedPrefixCode (succ k)) Q T m)) (woodinRecodedSuccessorOrder k (forcingRecodedCode (succ k) (woodinNormalizedPrefixCode (succ k)) Q T m))
    (woodinRecodedSuccessorMap k (forcingRecodedCode (succ k) (woodinNormalizedPrefixCode (succ k)) Q T m) m) at hf
  have he := woodinSparseSuccessorEncode_isomorphism (k := k) (c := (forcingRecodedCode (succ k) (woodinNormalizedPrefixCode (succ k)) Q T m)) hsp'
  rw [woodinSparseSuccessorMap, value_compose_of_mem_function hf.1 he.1 hz,
    sparsePairEncode_value_of_mem (W := woodinSparseSuccessorPool k (forcingRecodedCode (succ k) (woodinNormalizedPrefixCode (succ k)) Q T m)) hsp' (function_value_mem hf.1 hz),
    woodinRecodedSuccessorMap_value hΩ hAC hk hz]
  simp only [normalizedTwoStepIsoValue, kpair.π₁_kpair, kpair.π₂_kpair]

end ZFVP
