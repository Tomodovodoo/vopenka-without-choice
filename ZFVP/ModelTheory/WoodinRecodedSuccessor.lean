import ZFVP.ModelTheory.WoodinSupportSuccessorTransport
import ZFVP.ModelTheory.WoodinNormalizedPrefix
import ZFVP.ModelTheory.ForcingRecodedSystem
import ZFVP.ModelTheory.NormalizedIsomorphismDefinability

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def woodinNormalizedSuccessorCutoff (k : V) : V :=
  let s := woodinNormalizedStageCode k
  woodinPrefixCutoff ((forcingCodeP s) ‘ k) ((forcingCodeR s) ‘ k) ((forcingCodet s) ‘ k)
    ((kpair.π₂ (woodinIterationRec k)) ‘ k)

noncomputable def woodinRecodedSuccessorMap (k c m : V) : V :=
  let s := woodinNormalizedStageCode k
  let P := (forcingCodeP s) ‘ k
  let R := (forcingCodeR s) ‘ k
  let o := (forcingCodet s) ‘ k
  let κ := (kpair.π₂ (woodinIterationRec k)) ‘ k
  let δ := woodinNormalizedSuccessorCutoff k
  normalizedTwoStepIsoMap P R o δ (saturatedWoodinPrefixPosetName P R o κ δ)
    ((forcingCodeP c) ‘ k) ((forcingCodeR c) ‘ k) ((forcingCodet c) ‘ k) (m ‘ k)

instance woodinNormalizedSuccessorCutoff_definable : ℒₛₑₜ-function₁[V] woodinNormalizedSuccessorCutoff := by
  unfold woodinNormalizedSuccessorCutoff
  dsimp only
  apply Language.DefinableFunction₄.comp <;> definability

instance woodinRecodedSuccessorMap_definable : ℒₛₑₜ-function₃[V] woodinRecodedSuccessorMap := by
  unfold woodinRecodedSuccessorMap
  dsimp only
  apply normalizedTwoStepIsoMap_comp
  · definability
  · definability
  · definability
  · definability
  · apply Language.DefinableFunction₅.comp <;> definability
  · definability
  · definability
  · definability
  · definability

variable {Ω k Q T m : V} [IsOrdinal k]
local notation "s" => woodinNormalizedStageCode k
local notation "P" => (forcingCodeP s) ‘ k
local notation "R" => (forcingCodeR s) ‘ k
local notation "o" => (forcingCodet s) ‘ k
local notation "κ" => (kpair.π₂ (woodinIterationRec k)) ‘ k
local notation "δ" => woodinNormalizedSuccessorCutoff k
local notation "c" => forcingRecodedCode (succ k) (woodinNormalizedPrefixCode (succ k)) Q T m
local notation "A" => (forcingCodeP c) ‘ k
local notation "B" => (forcingCodeR c) ‘ k
local notation "top" => (forcingCodet c) ‘ k

theorem woodinNormalizedSuccessorCutoff_bounds
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hk : k ∈ Ω) :
    IsChoicelessInaccessible δ ∧ P ∈ hierarchy δ := by
  have hi := ((woodinIterationExit hΩ hAC).2.1 k hk).1.normalizationSuccessor_inputs hΩ
  have he := woodinNormalizedStage_prefix_cutoff hΩ hAC hk κ
  change _ = δ at he
  rw [he] at hi
  let := hi.2.2.1.1
  exact ⟨hi.2.2.1, subset_mem_hierarchy_limit hi.2.2.1.rankCriterion.2.2.1
    hi.2.2.2.1 woodinNormalizedStage_subset⟩

theorem woodinRecodedSuccessorMap_isomorphism
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) (hk : k ∈ Ω)
    (hm : ∀ i ∈ succ k, IsForcingIsomorphism
      ((forcingCodeP (woodinNormalizedPrefixCode (succ k))) ‘ i)
      ((forcingCodeR (woodinNormalizedPrefixCode (succ k))) ‘ i) (Q ‘ i) (T ‘ i) (m ‘ i))
    (hT : ∀ i ∈ succ k, IsForcingPreorder (Q ‘ i) (T ‘ i))
    (hQt : IsIterationTable (succ k) Q) (hTt : IsIterationTable (succ k) T)
    (hQrank : Q ‘ k ∈ hierarchy δ) :
    let ε := woodinPrefixCutoff A B top κ
    let U := saturatedWoodinPrefixPosetName A B top κ ε
    IsForcingIsomorphism ((forcingCodeP (woodinNormalizedStageCode (succ k))) ‘ (succ k))
      ((forcingCodeR (woodinNormalizedStageCode (succ k))) ‘ (succ k))
      (normalizedNameTwoStep A B top ε U)
      (nameTwoStepOrderOn A B (saturatedWoodinPrefixOrderName A B top κ ε)
        (normalizedNameTwoStep A B top ε U)) (woodinRecodedSuccessorMap k c m) := by
  let := hΩ.inaccessible.1
  have hsub : succ k ⊆ Ω := by
    intro i hi
    rcases mem_succ_iff.mp hi with rfl | hi
    · exact hk
    · exact IsOrdinal.toIsTransitive.mem_trans hi hk
  have hc := forcingRecoded_code (woodinNormalizedPrefixCode_valid hΩ hAC hsub) hm hT hQt hTt
  have hs := woodinNormalizedStageCode_valid hΩ hAC hk
  have hf := hm k (mem_succ_self k)
  rw [woodinNormalizedPrefix_successor hΩ hAC hk] at hf
  have hf' : IsForcingIsomorphism P R A B (m ‘ k) := by
    simpa only [forcingRecodedCode, forcingCodeP_code, forcingCodeR_code] using hf
  have hA : A ∈ hierarchy δ := by
    simpa only [forcingRecodedCode, forcingCodeP_code] using hQrank
  have hft : (m ‘ k) ‘ o = top := by
    simp only [forcingRecodedCode, forcingCodet_code, forcingRecodedTops_value (mem_succ_self k),
      woodinNormalizedPrefix_successor hΩ hAC hk]
  obtain ⟨hd, hP⟩ := woodinNormalizedSuccessorCutoff_bounds hΩ hAC hk
  obtain ⟨hp, hr⟩ := woodinNormalizedStage_successor_eq hΩ hAC hk
  dsimp only at hp hr ⊢
  rw [hp, hr]
  exact normalizedPrefixSuccessor_isomorphism hf' (hs.system.order.preorder k (mem_succ_self k))
    (hc.system.order.preorder k (mem_succ_self k)) (hs.system.tops.top k (mem_succ_self k))
    (hc.system.tops.top k (mem_succ_self k)) hft hd hP hA

end ZFVP
