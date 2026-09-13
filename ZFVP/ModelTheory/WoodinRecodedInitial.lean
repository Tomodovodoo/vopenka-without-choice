import ZFVP.ModelTheory.WoodinRecodedSuccessorNext

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def woodinRecodedInitialCarrier : V :=
  let P := ({∅} : V)
  let R := P ×ˢ P
  let δ := woodinPrefixCutoff P R ∅ woodinSeedCardinal
  normalizedNameTwoStep P R ∅ δ (saturatedWoodinPrefixPosetName P R ∅ woodinSeedCardinal δ)

noncomputable def woodinRecodedInitialOrder : V :=
  let P := ({∅} : V)
  let R := P ×ˢ P
  let δ := woodinPrefixCutoff P R ∅ woodinSeedCardinal
  nameTwoStepOrderOn P R (saturatedWoodinPrefixOrderName P R ∅ woodinSeedCardinal δ) woodinRecodedInitialCarrier

noncomputable def woodinRecodedInitialMaps : V := forcingFamilyNext ∅ ∅ (identity (woodinRecodedInitialCarrier : V))

noncomputable def woodinRecodedInitialCode : V :=
  forcingRecodedCode (succ ∅) (woodinNormalizedStageCode ∅)
    (forcingFamilyNext ∅ ∅ woodinRecodedInitialCarrier)
    (forcingFamilyNext ∅ ∅ woodinRecodedInitialOrder) woodinRecodedInitialMaps

local notation "N" => (woodinRecodedInitialCarrier : V)
local notation "T" => (woodinRecodedInitialOrder : V)

attribute [local aesop 5 (rule_sets := [Definability]) safe]
  Language.DefinableFunction₄.comp Language.DefinableFunction₅.comp

instance woodinRecodedInitialCarrier_definable : Language.DefinableFunction₀ ℒₛₑₜ (woodinRecodedInitialCarrier : V) := by
  unfold woodinRecodedInitialCarrier
  dsimp only
  apply Language.DefinableFunction₅.comp <;> definability

instance woodinRecodedInitialOrder_definable : Language.DefinableFunction₀ ℒₛₑₜ (woodinRecodedInitialOrder : V) := by
  unfold woodinRecodedInitialOrder
  dsimp only
  apply Language.DefinableFunction₄.comp <;> definability

instance woodinRecodedInitialMaps_definable : Language.DefinableFunction₀ ℒₛₑₜ (woodinRecodedInitialMaps : V) := by
  unfold woodinRecodedInitialMaps
  definability

instance woodinRecodedInitialCode_definable : Language.DefinableFunction₀ ℒₛₑₜ (woodinRecodedInitialCode : V) := by
  unfold woodinRecodedInitialCode
  apply Language.DefinableFunction₅.comp <;> definability

theorem woodinNormalizedStage_initial_dictionary {Ω : V} (hΩ : IsWoodinSupercompact Ω) :
    (forcingCodeP (woodinNormalizedStageCode (∅ : V))) ‘ ∅ = N ∧
      (forcingCodeR (woodinNormalizedStageCode (∅ : V))) ‘ ∅ = T := by
  have hn : (woodinNormalizationHistory (succ (∅ : V))) ‘ ∅ = woodinNormalizationInitialMap := by
    rw [woodinNormalizationHistory_value (mem_succ_self _), woodinNormalizationRec_rule]
    simp only [woodinNormalizationRule, ite_true]
  have hr := woodinNormalizationInitial_retraction hΩ
  obtain ⟨_, _, _, hI⟩ := woodinNormalizationInitial_inputs hΩ
  have ht : IsForcingPreorder N T := normalizedNameTwoStep_preorder (singletonForcing_preorder (∅ : V))
    (singletonForcing_top ∅) hI.posetName hI.orderName hI.preorder
  simp only [woodinNormalizedStageCode, forcingNormalizedCode, forcingCodeP_code, forcingCodeR_code,
    forcingNormalizationCarriers_value (mem_succ_self _), forcingNormalizationOrders_value (mem_succ_self _),
    hn, woodinIterationRec_initial, kpair.π₁_kpair]
  constructor
  · exact hr.fixedPoints_eq
  · rw [hr.fixedPoints_eq]
    exact hr.orderRestriction_eq ht

theorem woodinRecodedInitialOrder_preorder {Ω : V} (hΩ : IsWoodinSupercompact Ω) : IsForcingPreorder N T := by
  obtain ⟨_, _, _, hI⟩ := woodinNormalizationInitial_inputs hΩ
  exact normalizedNameTwoStep_preorder (singletonForcing_preorder ∅) (singletonForcing_top ∅)
    hI.posetName hI.orderName hI.preorder

theorem woodinRecodedInitial_family {Ω : V} (hΩ : IsWoodinSupercompact Ω) :
    ∀ i ∈ succ (∅ : V), IsForcingIsomorphism ((forcingCodeP (woodinNormalizedStageCode ∅)) ‘ i)
      ((forcingCodeR (woodinNormalizedStageCode ∅)) ‘ i)
      ((forcingFamilyNext ∅ ∅ N) ‘ i) ((forcingFamilyNext ∅ ∅ T) ‘ i) (woodinRecodedInitialMaps ‘ i) := by
  intro i hi
  have he : i = (∅ : V) := by simpa only [mem_succ_iff, not_mem_empty, or_false] using hi
  subst i
  rw [(woodinNormalizedStage_initial_dictionary hΩ).1, (woodinNormalizedStage_initial_dictionary hΩ).2]
  simp only [woodinRecodedInitialMaps, forcingFamilyNext_new]
  exact forcingAutomorphism_identity N T

theorem woodinRecodedInitialCode_valid {Ω : V}
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V) :
    IsForcingIterationCode (succ ∅) (woodinRecodedInitialCode : V) := by
  have h0 : (∅ : V) ∈ Ω := hΩ.inaccessible.regular.2.1 ∅ (by simp)
  apply forcingRecoded_code (woodinNormalizedStageCode_valid hΩ hAC h0) (woodinRecodedInitial_family hΩ)
    ?_ (forcingFamilyNext_table _ _ _) (forcingFamilyNext_table _ _ _)
  intro i hi
  have he : i = (∅ : V) := by simpa only [mem_succ_iff, not_mem_empty, or_false] using hi
  subst i
  simpa only [forcingFamilyNext_new] using woodinRecodedInitialOrder_preorder hΩ

theorem woodinRecodedInitial_small {Ω ξ : V}
    (hΩ : IsWoodinSupercompact Ω) (hAC : ¬InternalChoice V)
    (hξ : IsChoicelessInaccessible ξ) (hcard : (kpair.π₂ (woodinIterationRec (∅ : V))) ‘ ∅ ∈ ξ) :
    N ∈ hierarchy ξ := by
  rw [← (woodinNormalizedStage_initial_dictionary hΩ).1]
  exact woodinNormalizedStage_small hΩ hAC (hΩ.inaccessible.regular.2.1 ∅ (by simp)) hξ hcard

end ZFVP
