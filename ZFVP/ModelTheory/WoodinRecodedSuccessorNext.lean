import ZFVP.ModelTheory.WoodinRecodedSuccessor
import ZFVP.ModelTheory.WoodinRecodedInverseNext
import ZFVP.ModelTheory.ForcingRecodedPrefix

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def woodinRecodedSuccessorCarrier (k c : V) : V :=
  let P := (forcingCodeP c) ‘ k
  let R := (forcingCodeR c) ‘ k
  let o := (forcingCodet c) ‘ k
  let κ := (kpair.π₂ (woodinIterationRec k)) ‘ k
  let δ := woodinPrefixCutoff P R o κ
  normalizedNameTwoStep P R o δ (saturatedWoodinPrefixPosetName P R o κ δ)

noncomputable def woodinRecodedSuccessorOrder (k c : V) : V :=
  let P := (forcingCodeP c) ‘ k
  let R := (forcingCodeR c) ‘ k
  let o := (forcingCodet c) ‘ k
  let κ := (kpair.π₂ (woodinIterationRec k)) ‘ k
  let δ := woodinPrefixCutoff P R o κ
  nameTwoStepOrderOn P R (saturatedWoodinPrefixOrderName P R o κ δ) (woodinRecodedSuccessorCarrier k c)

noncomputable def woodinRecodedSuccessorNextCode (k Q T m : V) : V :=
  let c := forcingRecodedCode (succ k) (woodinNormalizedPrefixCode (succ k)) Q T m
  forcingRecodedCode (succ (succ k)) (woodinNormalizedStageCode (succ k))
    (forcingFamilyNext (succ k) Q (woodinRecodedSuccessorCarrier k c))
    (forcingFamilyNext (succ k) T (woodinRecodedSuccessorOrder k c))
    (forcingFamilyNext (succ k) m (woodinRecodedSuccessorMap k c m))

attribute [local aesop 5 (rule_sets := [Definability]) safe]
  Language.DefinableFunction₄.comp Language.DefinableFunction₅.comp

instance woodinRecodedSuccessorCarrier_definable : ℒₛₑₜ-function₂[V] woodinRecodedSuccessorCarrier := by
  unfold woodinRecodedSuccessorCarrier
  dsimp only
  apply Language.DefinableFunction₅.comp <;> definability

instance woodinRecodedSuccessorOrder_definable : ℒₛₑₜ-function₂[V] woodinRecodedSuccessorOrder := by
  unfold woodinRecodedSuccessorOrder
  dsimp only
  apply Language.DefinableFunction₄.comp <;> definability

instance woodinRecodedSuccessorNextCode_definable : ℒₛₑₜ-function₄[V] woodinRecodedSuccessorNextCode := by
  unfold woodinRecodedSuccessorNextCode
  dsimp only
  apply Language.DefinableFunction₅.comp <;> definability

variable {Ω k Q T m : V} [IsOrdinal k]
local notation "N" => woodinNormalizedPrefixCode (succ k)
local notation "C" => woodinNormalizedStageCode (succ k)
local notation "c" => forcingRecodedCode (succ k) N Q T m
local notation "A" => woodinRecodedSuccessorCarrier k c
local notation "B" => woodinRecodedSuccessorOrder k c
local notation "f" => woodinRecodedSuccessorMap k c m
local notation "next" => woodinRecodedSuccessorNextCode k Q T m

variable (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hk : succ k ∈ Ω)
variable (hm : ∀ i ∈ succ k, IsForcingIsomorphism
  ((forcingCodeP (woodinNormalizedPrefixCode (succ k))) ‘ i)
  ((forcingCodeR (woodinNormalizedPrefixCode (succ k))) ‘ i) (Q ‘ i) (T ‘ i) (m ‘ i))
variable (hT : ∀ i ∈ succ k, IsForcingPreorder (Q ‘ i) (T ‘ i))
variable (hQt : IsIterationTable (succ k) Q) (hTt : IsIterationTable (succ k) T)
variable (hQrank : Q ‘ k ∈ hierarchy (woodinNormalizedSuccessorCutoff k))

include hΩ hAC hk hm hT hQt hTt hQrank

theorem woodinRecodedSuccessorNext_family :
    ∀ i ∈ succ (succ k), IsForcingIsomorphism ((forcingCodeP C) ‘ i) ((forcingCodeR C) ‘ i)
      ((forcingFamilyNext (succ k) Q A) ‘ i) ((forcingFamilyNext (succ k) T B) ‘ i)
      ((forcingFamilyNext (succ k) m f) ‘ i) := by
  let := hΩ.inaccessible.1
  apply forcingRecoded_next_family
    (fun _ hi ↦ (woodinNormalizedStage_old_carrier_order hΩ hAC hk hi).1)
    (fun _ hi ↦ (woodinNormalizedStage_old_carrier_order hΩ hAC hk hi).2) hm
  exact woodinRecodedSuccessorMap_isomorphism hΩ hAC
    (IsOrdinal.toIsTransitive.mem_trans (mem_succ_self k) hk) hm hT hQt hTt hQrank

theorem woodinRecodedSuccessorNext_valid : IsForcingIterationCode (succ (succ k)) next := by
  let := hΩ.inaccessible.1
  apply forcingRecoded_next_code (woodinNormalizedStageCode_valid hΩ hAC hk)
    (fun _ hi ↦ (woodinNormalizedStage_old_carrier_order hΩ hAC hk hi).1)
    (fun _ hi ↦ (woodinNormalizedStage_old_carrier_order hΩ hAC hk hi).2) hm hT
    (woodinRecodedSuccessorMap_isomorphism hΩ hAC
      (IsOrdinal.toIsTransitive.mem_trans (mem_succ_self k) hk) hm hT hQt hTt hQrank)
  exact sep_subset

theorem woodinRecodedSuccessorNext_extends : ForcingCodeExtends c next := by
  let := hΩ.inaccessible.1
  have hs := woodinNormalizedPrefixCode_valid hΩ hAC (IsOrdinal.toIsTransitive.transitive _ hk)
  exact forcingRecoded_extends hs (woodinNormalizedStageCode_valid hΩ hAC hk)
    (woodinNormalizedStage_extends hΩ hAC hk)
    (fun _ hi ↦ mem_succ_iff.mpr (Or.inr hi))
    (fun _ hi ↦ (forcingFamilyNext_old hi).symm)
    (fun _ hi ↦ (forcingFamilyNext_old hi).symm)
    (fun _ hi ↦ (forcingFamilyNext_old hi).symm)
    (forcingRecoded_code hs hm hT hQt hTt)
    (woodinRecodedSuccessorNext_valid hΩ hAC hk hm hT hQt hTt hQrank)

theorem woodinRecodedSuccessorNext_restrictions :
    (forcingCodeP next) ↾ (succ k) = forcingCodeP c ∧ (forcingCodeR next) ↾ (succ k) = forcingCodeR c ∧
    (forcingCodeπ next) ↾ ((succ k) ×ˢ (succ k)) = forcingCodeπ c ∧
    (forcingCodeE next) ↾ ((succ k) ×ˢ (succ k)) = forcingCodeE c ∧
    (forcingCodeL next) ↾ ((succ k) ×ˢ (succ k)) = forcingCodeL c ∧
    (forcingCodet next) ↾ (succ k) = forcingCodet c := by
  let := hΩ.inaccessible.1
  have hs := woodinNormalizedPrefixCode_valid hΩ hAC (IsOrdinal.toIsTransitive.transitive _ hk)
  exact (woodinRecodedSuccessorNext_extends hΩ hAC hk hm hT hQt hTt hQrank).restrictions
    (forcingRecoded_code hs hm hT hQt hTt)
    (woodinRecodedSuccessorNext_valid hΩ hAC hk hm hT hQt hTt hQrank)
    (fun _ hi ↦ mem_succ_iff.mpr (Or.inr hi))

omit hΩ hAC hk hm hT hQt hTt hQrank [IsOrdinal k] in
theorem woodinRecodedSuccessorNext_carrier_order :
    (forcingCodeP next) ‘ (succ k) = A ∧ (forcingCodeR next) ‘ (succ k) = B := by
  simp only [woodinRecodedSuccessorNextCode, forcingRecodedCode, forcingCodeP_code,
    forcingCodeR_code, forcingFamilyNext_new, and_self]

end ZFVP
