import ZFVP.ModelTheory.ForcingNormalizationLimitFamily
import ZFVP.ModelTheory.SaturatedHartogsStage
import ZFVP.ModelTheory.WoodinInverseCodeDefinability

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

instance saturatedHartogsPosetName_uniform_definable :
    Language.DefinableFunction₅ ℒₛₑₜ (saturatedHartogsPosetName (V := V)) :=
  saturatedHartogsPosetNameFormula_defined.to_definable

noncomputable def woodinNormalizationInverseMap (θ s K m : V) : V :=
  let P := forcingInverseCodePoset θ s
  let R := forcingInverseCodeOrder θ s
  let o := forcingInverseCodeTop θ s
  let c := forcingInverseSourceCutoff θ s (woodinLimitCardinal K)
  let r := forcingNormalizationInverseMap θ s m
  let N := forcingMapFixedPoints P r
  normalizedBaseTwoStepMap P R N (forcingOrderRestriction N R) o c
    (saturatedHartogsPosetName P R o (woodinLimitCardinal K) c) r

/-- Insert the completed inverse normalizer at the original limit index. -/
noncomputable def woodinNormalizationInverse (θ s K m : V) : V :=
  forcingFamilyNext θ m (woodinNormalizationInverseMap θ s K m)

instance woodinNormalizationInverseMap_definable : ℒₛₑₜ-function₄[V] woodinNormalizationInverseMap := by
  unfold woodinNormalizationInverseMap
  dsimp only
  apply normalizedBaseTwoStepMap_comp
  · definability
  · definability
  · definability
  · definability
  · definability
  · definability
  · apply Language.DefinableFunction₅.comp <;> definability
  · definability

instance woodinNormalizationInverse_definable : ℒₛₑₜ-function₄[V] woodinNormalizationInverse := by
  unfold woodinNormalizationInverse
  apply Language.DefinableFunction₃.comp
  · definability
  · definability
  · apply Language.DefinableFunction₄.comp <;> definability

theorem woodinNormalizationInverse_old {θ s K m i : V} (hi : i ∈ θ) :
    (woodinNormalizationInverse θ s K m) ‘ i = m ‘ i := forcingFamilyNext_old hi

theorem woodinNormalizationInverse_new (θ s K m : V) :
    (woodinNormalizationInverse θ s K m) ‘ θ = woodinNormalizationInverseMap θ s K m :=
  forcingFamilyNext_new _ _ _

theorem woodinNormalizationInverse_table (θ s K m : V) :
    IsIterationTable (succ θ) (woodinNormalizationInverse θ s K m) := forcingFamilyNext_table _ _ _

variable {θ s K m : V}
local notation "P" => forcingInverseCodePoset θ s
local notation "R" => forcingInverseCodeOrder θ s
local notation "o" => forcingInverseCodeTop θ s
local notation "γ" => woodinLimitCardinal K
local notation "c" => forcingInverseSourceCutoff θ s γ
local notation "Q" => saturatedHartogsPosetName P R o γ c
local notation "S" => saturatedHartogsOrderName P R o γ c
local notation "r" => forcingNormalizationInverseMap θ s m
local notation "N" => forcingMapFixedPoints P r
local notation "T" => forcingOrderRestriction N R

theorem woodinInverseSourceCode_poset :
    (forcingCodeP (woodinInverseSourceCode θ s K)) ‘ θ = twoStepConditions P R Q ∅ := by
  simpa only [woodinIterationStage, woodinStagePoset_code, saturatedHartogsStageAt] using
    congrArg woodinStagePoset (woodinInverseSourceCode_stageAt θ s K)

theorem woodinInverseSourceCode_order :
    (forcingCodeR (woodinInverseSourceCode θ s K)) ‘ θ = twoStepOrder P R Q S ∅ := by
  simpa only [woodinIterationStage, woodinStageOrder_code, saturatedHartogsStageAt] using
    congrArg woodinStageOrder (woodinInverseSourceCode_stageAt θ s K)

theorem woodinInverseSourceCode_top : (forcingCodet (woodinInverseSourceCode θ s K)) ‘ θ = ⟨o, ∅⟩ₖ := by
  simpa only [woodinIterationStage, woodinStageTop_code, saturatedHartogsStageAt] using
    congrArg woodinStageTop (woodinInverseSourceCode_stageAt θ s K)

theorem saturatedHartogs_twoStep_eq_bounded {A B one κ δ : V}
    (hR : IsForcingPreorder A B) (hc : IsChoicelessInaccessible δ) (hP : A ∈ hierarchy δ) :
    twoStepConditions A B (saturatedHartogsPosetName A B one κ δ) ∅ =
      boundedNameTwoStep A B δ (saturatedHartogsPosetName A B one κ δ) :=
  saturatedTwoStep_eq_boundedNameTwoStep hR hc hP

theorem saturatedHartogs_twoStepOrder_eq_bounded {A B one κ δ : V}
    (hR : IsForcingPreorder A B) (hc : IsChoicelessInaccessible δ) (hP : A ∈ hierarchy δ) :
    twoStepOrder A B (saturatedHartogsPosetName A B one κ δ) (saturatedHartogsOrderName A B one κ δ) ∅ =
      nameTwoStepOrderOn A B (saturatedHartogsOrderName A B one κ δ)
        (boundedNameTwoStep A B δ (saturatedHartogsPosetName A B one κ δ)) :=
  saturatedTwoStepOrder_eq_nameTwoStepOrderOn hR hc hP

theorem forcingNormalizationInverse_fixed_retraction (hs : IsForcingIterationCode θ s)
    (h : IsForcingNormalizationFamily θ s m) : IsForcingRetraction N T P R r := by
  have hr := forcingNormalizationInverse_retraction hs h
  have ht := forcingThreadOrder_preorder hs.system.order.preorder
    (fun f (hf : f ∈ forcingInverseLimit θ (forcingNormalizationCarriers θ s m)
      (forcingCodeπ s) (forcingCodeUniverse s)) i hi ↦
      h.inclusion i hi _ (((mem_forcingInverseLimit_iff _ _ _ _ _).mp hf).2.1 i hi))
  simp only [forcingInverseCode, forcingThreadCode_poset, forcingThreadCode_order] at hr
  change IsForcingRetraction _ _ P R r at hr
  rw [hr.fixedPoints_eq, hr.orderRestriction_eq ht]
  exact hr

theorem IsWoodinIteration.normalizationInverse_inputs {Ω : V} [IsOrdinal θ]
    (hs : IsWoodinIteration Ω θ s K) (hΩ : IsWoodinSupercompact Ω) (hθ : θ ∈ Ω) (h0 : ∅ ∈ θ)
    (hlim : ∀ i ∈ θ, succ i ∈ θ)
    (hγ : ∀ p ∈ P, p ∈ forcingFormula P R (regularCardinalFormula.or limitOfRegularCardinalsFormula)
      (standardTuple ![checkName o γ]))
    (hDC : ∀ p ∈ P, p ∈ forcingFormula P R dependentChoiceAtFormula (standardTuple ![checkName o γ])) :
    IsForcingPreorder P R ∧ IsForcingTop P R o ∧ IsChoicelessInaccessible c ∧ P ∈ hierarchy c ∧
      IsForcingIterand P R Q S ∅ := by
  obtain ⟨_, hc⟩ := hs.inverse_sourceCutoff hΩ hθ h0 hγ hDC
  have hp := hs.inverse_small_above_limit hlim hc.2.1 hc.1
  have col := hs.code.system.inverseColumn h0 hs.code.subset_universe
  have ht : IsForcingTop P R o := col.tops.top
  have hk : ∀ p ∈ P, p ∈ forcingFormula P R regularCardinalFormula
      (standardTuple ![hartogsNumberName P R (checkName o γ)]) := by
    intro p hp
    exact hartogsNumberName_forces_regular col.order.preorder ht hp
      ⟨checkName o γ, checkName_isName ht.1 _⟩ (hγ p hp) (hDC p hp)
  exact ⟨col.order.preorder, ht, hc.2.1, hp.1, saturatedHartogsCollapse_iterand col.order.preorder ht hc.2.1 hk⟩

theorem woodinNormalizationInverseMap_retraction
    (hr : IsForcingRetraction N T P R r) (hR : IsForcingPreorder P R) (ht : IsForcingTop P R o)
    (hc : IsChoicelessInaccessible c) (hP : P ∈ hierarchy c) (hI : IsForcingIterand P R Q S ∅)
    (ho : r ‘ o = o) (he : ∀ p ∈ P, ⟨r ‘ p, p⟩ₖ ∈ R ∧ ⟨p, r ‘ p⟩ₖ ∈ R) :
    IsForcingRetraction (normalizedNameTwoStep N T o c (nameAction r Q))
      (nameTwoStepOrderOn N T (nameAction r S) (normalizedNameTwoStep N T o c (nameAction r Q)))
      ((forcingCodeP (woodinInverseSourceCode θ s K)) ‘ θ)
      ((forcingCodeR (woodinInverseSourceCode θ s K)) ‘ θ) (woodinNormalizationInverseMap θ s K m) := by
  have hT := forcingOrderRestriction_preorder hR hr.inclusion
  have hone : o ∈ N := mem_sep_iff.mpr ⟨ht.1, ho⟩
  rw [woodinInverseSourceCode_poset, woodinInverseSourceCode_order,
    saturatedHartogs_twoStep_eq_bounded hR hc hP, saturatedHartogs_twoStepOrder_eq_bounded hR hc hP]
  exact normalizedBaseTwoStepMap_retraction hr hR hT ht hone hc hP he hI

theorem forcingNormalizationInverse_base [IsOrdinal θ] (hs : IsForcingIterationCode θ s)
    (h : IsForcingNormalizationFamily θ s m) (h0 : ∅ ∈ θ) :
    IsForcingRetraction N T P R r ∧ r ‘ o = o ∧
      ∀ p ∈ P, ⟨r ‘ p, p⟩ₖ ∈ R ∧ ⟨p, r ‘ p⟩ₖ ∈ R := by
  refine ⟨forcingNormalizationInverse_fixed_retraction hs h, ?_, ?_⟩
  · simpa only [forcingInverseCode, forcingThreadCode_top, forcingInverseCodeTop] using
      forcingNormalizationInverse_top hs h h0
  · intro p hp
    have hp' : p ∈ (forcingCodeP (forcingInverseCode θ s)) ‘ θ := by
      simpa only [forcingInverseCode, forcingThreadCode_poset, forcingInverseCodePoset] using hp
    simpa only [forcingInverseCode, forcingThreadCode_order, forcingInverseCodeOrder, forcingInverseCodePoset] using
      forcingNormalizationInverse_equivalent hs h hp'

theorem woodinNormalizationInverseMap_prefix {z : V}
    (hr : IsForcingRetraction N T P R r) (hR : IsForcingPreorder P R) (ht : IsForcingTop P R o)
    (hc : IsChoicelessInaccessible c) (hP : P ∈ hierarchy c) (hI : IsForcingIterand P R Q S ∅)
    (ho : r ‘ o = o) (he : ∀ p ∈ P, ⟨r ‘ p, p⟩ₖ ∈ R ∧ ⟨p, r ‘ p⟩ₖ ∈ R)
    (hz : z ∈ (forcingCodeP (woodinInverseSourceCode θ s K)) ‘ θ) :
    kpair.π₁ ((woodinNormalizationInverseMap θ s K m) ‘ z) = r ‘ (kpair.π₁ z) := by
  have hT := forcingOrderRestriction_preorder hR hr.inclusion
  have hone : o ∈ N := mem_sep_iff.mpr ⟨ht.1, ho⟩
  rw [woodinInverseSourceCode_poset, saturatedHartogs_twoStep_eq_bounded hR hc hP] at hz
  exact normalizedBaseTwoStepMap_prefix hr hR hT ht hone hc hP he hI hz

theorem woodinNormalizationInverseMap_empty_tail {p : V}
    (hr : IsForcingRetraction N T P R r) (hR : IsForcingPreorder P R) (ht : IsForcingTop P R o)
    (hc : IsChoicelessInaccessible c) (hP : P ∈ hierarchy c) (hI : IsForcingIterand P R Q S ∅)
    (ho : r ‘ o = o) (he : ∀ q ∈ P, ⟨r ‘ q, q⟩ₖ ∈ R ∧ ⟨q, r ‘ q⟩ₖ ∈ R)
    (hp : p ∈ P) : (woodinNormalizationInverseMap θ s K m) ‘ ⟨p, ∅⟩ₖ = ⟨r ‘ p, ∅⟩ₖ := by
  have hT := forcingOrderRestriction_preorder hR hr.inclusion
  have hone : o ∈ N := mem_sep_iff.mpr ⟨ht.1, ho⟩
  exact normalizedBaseTwoStepMap_empty_tail hr hR hT ht hone hc hP he hI hp

theorem woodinNormalizationInverseMap_top
    (hr : IsForcingRetraction N T P R r) (hR : IsForcingPreorder P R) (ht : IsForcingTop P R o)
    (hc : IsChoicelessInaccessible c) (hP : P ∈ hierarchy c) (hI : IsForcingIterand P R Q S ∅)
    (ho : r ‘ o = o) (he : ∀ p ∈ P, ⟨r ‘ p, p⟩ₖ ∈ R ∧ ⟨p, r ‘ p⟩ₖ ∈ R) :
    (woodinNormalizationInverseMap θ s K m) ‘ ((forcingCodet (woodinInverseSourceCode θ s K)) ‘ θ) =
      (forcingCodet (woodinInverseSourceCode θ s K)) ‘ θ := by
  rw [woodinInverseSourceCode_top, woodinNormalizationInverseMap_empty_tail hr hR ht hc hP hI ho he ht.1, ho]

theorem woodinNormalizationInverseMap_equivalent {z : V}
    (hr : IsForcingRetraction N T P R r) (hR : IsForcingPreorder P R) (ht : IsForcingTop P R o)
    (hc : IsChoicelessInaccessible c) (hP : P ∈ hierarchy c) (hI : IsForcingIterand P R Q S ∅)
    (ho : r ‘ o = o) (he : ∀ p ∈ P, ⟨r ‘ p, p⟩ₖ ∈ R ∧ ⟨p, r ‘ p⟩ₖ ∈ R)
    (hz : z ∈ (forcingCodeP (woodinInverseSourceCode θ s K)) ‘ θ) :
    ⟨(woodinNormalizationInverseMap θ s K m) ‘ z, z⟩ₖ ∈ (forcingCodeR (woodinInverseSourceCode θ s K)) ‘ θ ∧
      ⟨z, (woodinNormalizationInverseMap θ s K m) ‘ z⟩ₖ ∈ (forcingCodeR (woodinInverseSourceCode θ s K)) ‘ θ := by
  have hT := forcingOrderRestriction_preorder hR hr.inclusion
  have hone : o ∈ N := mem_sep_iff.mpr ⟨ht.1, ho⟩
  rw [woodinInverseSourceCode_poset, saturatedHartogs_twoStep_eq_bounded hR hc hP] at hz
  rw [woodinInverseSourceCode_order, saturatedHartogs_twoStepOrder_eq_bounded hR hc hP]
  exact normalizedBaseTwoStepMap_equivalent hr hR hT ht hone hc hP he hI hz

end ZFVP
