import ZFVP.ModelTheory.WoodinRecodedInitial
import ZFVP.ModelTheory.SparseNormalizedTwoStep
import ZFVP.SetTheory.WoodinSourceIndex

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

local notation "P" => ({∅} : V)
local notation "R" => (P ×ˢ P)
local notation "κ" => (woodinSeedCardinal : V)
local notation "c" => woodinPrefixCutoff P R ∅ κ
local notation "Q" => saturatedWoodinPrefixPosetName P R ∅ κ c
local notation "S" => saturatedWoodinPrefixOrderName P R ∅ κ c
local notation "W" => normalizedNamePool P R ∅ c Q

noncomputable def woodinSparseInitialCarrier : V := sparseNormalizedTwoStep (succ ∅) P R ∅ c Q

noncomputable def woodinSparseInitialOrder : V := sparseNormalizedTwoStepOrder (succ ∅) P R ∅ c Q S

noncomputable def woodinSparseInitialMap : V := sparsePairEncode (succ ∅) P W

attribute [local aesop 5 (rule_sets := [Definability]) safe]
  Language.DefinableFunction₄.comp Language.DefinableFunction₅.comp

instance woodinSparseInitialCarrier_definable : Language.DefinableFunction₀ ℒₛₑₜ (woodinSparseInitialCarrier : V) := by
  unfold woodinSparseInitialCarrier sparseNormalizedTwoStep
  apply Language.DefinableFunction₃.comp <;> definability

instance woodinSparseInitialOrder_definable : Language.DefinableFunction₀ ℒₛₑₜ (woodinSparseInitialOrder : V) := by
  unfold woodinSparseInitialOrder sparseNormalizedTwoStepOrder sparseNormalizedTwoStep
  apply Language.DefinableFunction₃.comp <;> definability

instance woodinSparseInitialMap_definable : Language.DefinableFunction₀ ℒₛₑₜ (woodinSparseInitialMap : V) := by
  unfold woodinSparseInitialMap
  apply Language.DefinableFunction₃.comp <;> definability

theorem woodinSparseInitial_isomorphism :
    IsForcingIsomorphism (woodinRecodedInitialCarrier : V) woodinRecodedInitialOrder
      woodinSparseInitialCarrier woodinSparseInitialOrder woodinSparseInitialMap := by
  apply sparsePairEncode_isomorphism
  intro p hp
  have he : p = (∅ : V) := by simpa using hp
  subst p
  exact isSparseFunctionOn_empty _

theorem woodinSparseInitialMap_isomorphism {Ω : V} (hΩ : IsWoodinSupercompact Ω) :
    IsForcingIsomorphism ((forcingCodeP (woodinNormalizedStageCode (∅ : V))) ‘ ∅)
      ((forcingCodeR (woodinNormalizedStageCode (∅ : V))) ‘ ∅)
      woodinSparseInitialCarrier woodinSparseInitialOrder woodinSparseInitialMap := by
  rw [(woodinNormalizedStage_initial_dictionary hΩ).1, (woodinNormalizedStage_initial_dictionary hΩ).2]
  exact woodinSparseInitial_isomorphism

theorem woodinSparseInitialMap_value {τ : V} (hτ : τ ∈ W) :
    (woodinSparseInitialMap : V) ‘ ⟨∅, τ⟩ₖ = sparseAppend (succ ∅) ∅ τ := by
  apply sparsePairEncode_value
  · intro p hp
    have he : p = (∅ : V) := by simpa using hp
    subst p
    exact isSparseFunctionOn_empty _
  · simp
  · exact hτ

theorem woodinSparseInitial_preorder {Ω : V} (hΩ : IsWoodinSupercompact Ω) :
    IsForcingPreorder (woodinSparseInitialCarrier : V) woodinSparseInitialOrder :=
  woodinSparseInitial_isomorphism.target_preorder (woodinRecodedInitialOrder_preorder hΩ)
    (forcingPullbackOrder_subset _ _ _)

theorem woodinSparseInitial_empty_top {Ω : V} (hΩ : IsWoodinSupercompact Ω) :
    IsForcingTop (woodinSparseInitialCarrier : V) woodinSparseInitialOrder ∅ := by
  obtain ⟨hc, hp, _, hi⟩ := woodinNormalizationInitial_inputs hΩ
  let := hc.1
  have ht := normalizedNameTwoStep_top (singletonForcing_preorder ∅) (singletonForcing_top ∅) hp hi
  have he : (woodinSparseInitialMap : V) ‘ ⟨∅, ∅⟩ₖ = ∅ := by
    rw [woodinSparseInitialMap_value (kpair_mem_iff.mp ht.1).2, sparseAppend_empty]
  have hm := function_value_mem woodinSparseInitial_isomorphism.1 ht.1
  refine ⟨he ▸ hm, ?_⟩
  intro q hq
  obtain ⟨p, hp, rfl⟩ := woodinSparseInitial_isomorphism.surjective q hq
  rw [← he]
  exact (woodinSparseInitial_isomorphism.2.2.2 p hp _ ht.1).mp (ht.2 p hp)

theorem woodinSparseInitial_subset_hierarchy {Ω : V} (hΩ : IsWoodinSupercompact Ω) :
    (woodinSparseInitialCarrier : V) ⊆ hierarchy c := by
  obtain ⟨hc, hp, _, _⟩ := woodinNormalizationInitial_inputs hΩ
  let := hc.1
  apply sparseNormalizedTwoStep_subset_hierarchy hc.rankCriterion.2.2.1
  · have he : succ (∅ : V) = {∅} := by
      apply mem_ext
      intro x
      simp [mem_succ_iff]
    rwa [he]
  · exact (hierarchy_transitive c).transitive _ hp

theorem woodinSparseInitial_sparse {q : V} (hq : q ∈ (woodinSparseInitialCarrier : V)) :
    IsSparseFunctionOn (succ (woodinSourceIndex ∅)) q := by
  rw [woodinSourceIndex_natural (show (∅ : V) ∈ (ω : V) by simp)]
  exact (mem_sparseNormalizedTwoStep_iff.mp hq).1

theorem woodinSparseInitialMap_top {Ω : V} (hΩ : IsWoodinSupercompact Ω) :
    (woodinSparseInitialMap : V) ‘ ((forcingCodet (woodinNormalizedStageCode ∅)) ‘ ∅) = ∅ := by
  have he : (forcingCodet (woodinNormalizedStageCode (∅ : V))) ‘ ∅ = ⟨∅, ∅⟩ₖ := by
    simpa only [woodinNormalizedStageCode, forcingNormalizedCode, forcingCodet_code,
      woodinIterationRec_initial, kpair.π₁_kpair] using (woodinInitialCode_top_zero (V := V))
  obtain ⟨hc, hp, _, hi⟩ := woodinNormalizationInitial_inputs hΩ
  let := hc.1
  have ht := normalizedNameTwoStep_top (singletonForcing_preorder ∅) (singletonForcing_top ∅) hp hi
  rw [he, woodinSparseInitialMap_value (kpair_mem_iff.mp ht.1).2, sparseAppend_empty]

theorem woodinSparseInitial_small {Ω ξ : V} (hΩ : IsWoodinSupercompact Ω)
    (hξ : IsChoicelessInaccessible ξ) (hcard : (kpair.π₂ (woodinIterationRec (∅ : V))) ‘ ∅ ∈ ξ) :
    (woodinSparseInitialCarrier : V) ∈ hierarchy ξ := by
  let := hξ.1
  obtain ⟨hc, _, _, _⟩ := woodinNormalizationInitial_inputs hΩ
  let := hc.1
  have he : (kpair.π₂ (woodinIterationRec (∅ : V))) ‘ ∅ = c := by
    simp only [woodinIterationRec_initial, kpair.π₂_kpair, woodinInitialCardinals, forcingFamilyNext_new,
      woodinInitialStage, woodinSuccessorStep, woodinSuccessorAt, woodinStageCardinal_code,
      woodinSeedStage, woodinStagePoset_code, woodinStageOrder_code, woodinStageTop_code]
  apply subset_mem_hierarchy_limit hξ.rankCriterion.2.2.1 ?_ (woodinSparseInitial_subset_hierarchy hΩ)
  rw [mem_hierarchy_iff_rank_mem, rank_hierarchy]
  rwa [he] at hcard

end ZFVP
