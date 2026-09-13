import ZFVP.ModelTheory.WoodinIterationInitial
import ZFVP.ModelTheory.NormalizedMapDefinability

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

local notation "P" => ({∅} : V)
local notation "R" => (P ×ˢ P)
local notation "κ" => (woodinSeedCardinal : V)
local notation "c" => woodinPrefixCutoff P R ∅ κ
local notation "Q" => saturatedWoodinPrefixPosetName P R ∅ κ c
local notation "S" => saturatedWoodinPrefixOrderName P R ∅ κ c
local notation "N" => normalizedNameTwoStep P R ∅ c Q
local notation "T" => nameTwoStepOrderOn P R S N

noncomputable def woodinNormalizationInitialMap : V := normalizedTwoStepRetraction P R ∅ c Q

noncomputable def woodinNormalizationInitial : V :=
  forcingFamilyNext ∅ ∅ woodinNormalizationInitialMap

theorem woodinNormalizationInitial_value :
    (woodinNormalizationInitial : V) ‘ ∅ = woodinNormalizationInitialMap :=
  forcingFamilyNext_new _ _ _

theorem woodinNormalizationInitial_table : IsIterationTable (succ ∅) (woodinNormalizationInitial : V) :=
  forcingFamilyNext_table _ _ _

theorem woodinNormalizationInitial_inputs {Ω : V} (hΩ : IsWoodinSupercompact Ω) :
    IsChoicelessInaccessible c ∧ P ∈ hierarchy c ∧ κ ⊆ c ∧ IsForcingIterand P R Q S ∅ := by
  let := hΩ.inaccessible.1
  have hx := woodinSeedStage_stage (V := V)
  have hs := woodinSeedStage_small (V := V)
  have hb : woodinStageCardinal (woodinSeedStage : V) ∈ Ω := by
    simpa only [woodinSeedStage, woodinStageCardinal_code] using woodinSeedCardinal_lt hΩ
  have hp := hs Ω hΩ.inaccessible hb
  have hr := hx.order_mem_hierarchy hΩ.inaccessible.rankCriterion.2.2.1 hp
  obtain ⟨d, _, hd⟩ := hΩ.strictPrefixCutoff hx.1 hx.2.1 hp hr hb hx.2.2.2.1 hx.2.2.2.2
  have hc : IsWoodinPrefixCutoff P R ∅ κ c := by
    simpa only [woodinSeedStage, woodinStagePoset_code, woodinStageOrder_code,
      woodinStageTop_code, woodinStageCardinal_code] using (woodinPrefixCutoff_spec hd).2.1
  let := hc.2.1.1
  have hpc : P ∈ hierarchy c := by
    simpa only [woodinSeedStage, woodinStagePoset_code] using hs c hc.2.1
      (by simpa only [woodinSeedStage, woodinStageCardinal_code] using hc.1)
  have hκc : κ ⊆ c := IsOrdinal.toIsTransitive.transitive _ hc.1
  refine ⟨hc.2.1, hpc, hκc, saturatedWoodinPrefix_iterand (singletonForcing_preorder ∅)
    (singletonForcing_top ∅) hc.2.1 hpc hκc ?_⟩
  simpa only [woodinSeedStage, woodinStagePoset_code, woodinStageOrder_code,
    woodinStageTop_code, woodinStageCardinal_code] using hx.2.2.2.1

theorem woodinInitialCode_poset_zero :
    (forcingCodeP (woodinInitialCode : V)) ‘ ∅ = twoStepConditions P R Q ∅ := by
  simp [woodinInitialCode, forcingInitialCode, forcingFamilyNext_new, woodinInitialStage,
    woodinSeedStage, woodinSuccessorStep, woodinSuccessorAt]

theorem woodinInitialCode_order_zero :
    (forcingCodeR (woodinInitialCode : V)) ‘ ∅ = twoStepOrder P R Q S ∅ := by
  simp [woodinInitialCode, forcingInitialCode, forcingFamilyNext_new, woodinInitialStage,
    woodinSeedStage, woodinSuccessorStep, woodinSuccessorAt]

theorem woodinInitialCode_top_zero : (forcingCodet (woodinInitialCode : V)) ‘ ∅ = ⟨∅, ∅⟩ₖ := by
  simp [woodinInitialCode, forcingInitialCode, forcingFamilyNext_new, woodinInitialStage,
    woodinSeedStage, woodinSuccessorStep, woodinSuccessorAt]

theorem woodinNormalizationInitial_retraction {Ω : V} (hΩ : IsWoodinSupercompact Ω) :
    IsForcingRetraction N T ((forcingCodeP (woodinInitialCode : V)) ‘ ∅)
      ((forcingCodeR (woodinInitialCode : V)) ‘ ∅) woodinNormalizationInitialMap := by
  obtain ⟨hc, hp, _, hi⟩ := woodinNormalizationInitial_inputs hΩ
  let := hc.1
  rw [woodinInitialCode_poset_zero, woodinInitialCode_order_zero,
    saturatedWoodinPrefix_twoStep_eq_bounded (singletonForcing_preorder ∅) hc hp,
    saturatedWoodinPrefix_twoStepOrder_eq_bounded (singletonForcing_preorder ∅) hc hp]
  exact normalizedTwoStepRetraction_spec (singletonForcing_preorder ∅) (singletonForcing_top ∅)
    hc.rankCriterion.2.2.1 hp hi

theorem woodinNormalizationInitial_top {Ω : V} (hΩ : IsWoodinSupercompact Ω) :
    (woodinNormalizationInitialMap : V) ‘ ((forcingCodet woodinInitialCode) ‘ ∅) =
      (forcingCodet woodinInitialCode) ‘ ∅ := by
  obtain ⟨hc, hp, _, hi⟩ := woodinNormalizationInitial_inputs hΩ
  let := hc.1
  rw [woodinInitialCode_top_zero]
  exact (woodinNormalizationInitial_retraction hΩ).fixes _
    (normalizedNameTwoStep_top (singletonForcing_preorder ∅) (singletonForcing_top ∅) hp hi).1

theorem woodinNormalizationInitial_equivalent {Ω z : V} (hΩ : IsWoodinSupercompact Ω)
    (hz : z ∈ (forcingCodeP (woodinInitialCode : V)) ‘ ∅) :
    ⟨(woodinNormalizationInitialMap : V) ‘ z, z⟩ₖ ∈ (forcingCodeR (woodinInitialCode : V)) ‘ ∅ ∧
      ⟨z, (woodinNormalizationInitialMap : V) ‘ z⟩ₖ ∈ (forcingCodeR (woodinInitialCode : V)) ‘ ∅ := by
  obtain ⟨hc, hp, _, hi⟩ := woodinNormalizationInitial_inputs hΩ
  let := hc.1
  have hr := woodinNormalizationInitial_retraction hΩ
  have hn := function_value_mem hr.maps hz
  have ht := normalizedNameTwoStep_preorder (singletonForcing_preorder ∅)
    (singletonForcing_top ∅) hi.posetName hi.orderName hi.preorder (δ := c)
  refine ⟨?_, (hr.below z hz _ hn).mpr (ht.2.1 _ hn)⟩
  rw [woodinInitialCode_poset_zero,
    saturatedWoodinPrefix_twoStep_eq_bounded (singletonForcing_preorder ∅) hc hp] at hz
  rw [woodinInitialCode_order_zero,
    saturatedWoodinPrefix_twoStepOrder_eq_bounded (singletonForcing_preorder ∅) hc hp]
  exact normalizedTwoStepRetraction_below (singletonForcing_preorder ∅) (singletonForcing_top ∅)
    hc.rankCriterion.2.2.1 hp hi z hz

theorem woodinNormalizationInitial_projection_coherent {Ω z : V} (hΩ : IsWoodinSupercompact Ω)
    (hz : z ∈ (forcingCodeP (woodinInitialCode : V)) ‘ ∅) :
    ((forcingCodeπ (woodinInitialCode : V)) ‘ ⟨∅, ∅⟩ₖ) ‘ ((woodinNormalizationInitialMap : V) ‘ z) =
      (woodinNormalizationInitialMap : V) ‘ (((forcingCodeπ woodinInitialCode) ‘ ⟨∅, ∅⟩ₖ) ‘ z) := by
  have hr := woodinNormalizationInitial_retraction hΩ
  have hm := hr.inclusion _ (function_value_mem hr.maps hz)
  have hs := (woodinInitialCode_iteration hΩ).code.system
  have hid : ∀ w ∈ (forcingCodeP (woodinInitialCode : V)) ‘ ∅,
      ((forcingCodeπ woodinInitialCode) ‘ ⟨∅, ∅⟩ₖ) ‘ w = w := by
    intro w hw
    have hh := hs.split.retraction ∅ (mem_succ_self ∅) ∅ (mem_succ_self ∅) (subset_refl _) w hw
    rwa [hs.split.secId ∅ (mem_succ_self ∅) w hw] at hh
  rw [hid _ hm, hid _ hz]

theorem woodinNormalizationInitial_section_coherent {Ω z : V} (hΩ : IsWoodinSupercompact Ω)
    (hz : z ∈ (forcingCodeP (woodinInitialCode : V)) ‘ ∅) :
    (woodinNormalizationInitialMap : V) ‘ (((forcingCodeE woodinInitialCode) ‘ ⟨∅, ∅⟩ₖ) ‘ z) =
      ((forcingCodeE (woodinInitialCode : V)) ‘ ⟨∅, ∅⟩ₖ) ‘ ((woodinNormalizationInitialMap : V) ‘ z) := by
  have hr := woodinNormalizationInitial_retraction hΩ
  have hm := hr.inclusion _ (function_value_mem hr.maps hz)
  have hs := (woodinInitialCode_iteration hΩ).code.system
  rw [hs.split.secId ∅ (mem_succ_self ∅) _ hz,
    hs.split.secId ∅ (mem_succ_self ∅) _ hm]

end ZFVP
