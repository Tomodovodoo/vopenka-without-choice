import ZFVP.ModelTheory.RetractedBaseTwoStep
import ZFVP.ModelTheory.NormalizedWoodinPrefix
import ZFVP.SetTheory.ForcingRetractionComposition

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- First retract the preceding base and all name conditions, then apply the
specified normalization retraction over that base. -/
noncomputable def normalizedBaseTwoStepMap (P R N T one δ Q m : V) : V :=
  compose (retractedBaseTwoStepMap P R δ Q m)
    (normalizedTwoStepRetraction N T one δ (nameAction m Q))

theorem normalizedBaseTwoStepMap_retraction {P R N T one δ Q S m : V}
    (hr : IsForcingRetraction N T P R m) (hR : IsForcingPreorder P R) (hT : IsForcingPreorder N T)
    (ht : IsForcingTop P R one) (hone : one ∈ N)
    (hδ : IsChoicelessInaccessible δ) (hP : P ∈ hierarchy δ)
    (he : ∀ p ∈ P, ⟨m ‘ p, p⟩ₖ ∈ R ∧ ⟨p, m ‘ p⟩ₖ ∈ R)
    (hI : IsForcingIterand P R Q S ∅) :
    IsForcingRetraction (normalizedNameTwoStep N T one δ (nameAction m Q))
      (nameTwoStepOrderOn N T (nameAction m S) (normalizedNameTwoStep N T one δ (nameAction m Q)))
      (boundedNameTwoStep P R δ Q) (nameTwoStepOrderOn P R S (boundedNameTwoStep P R δ Q))
      (normalizedBaseTwoStepMap P R N T one δ Q m) := by
  let := hδ.1
  have hNδ := subset_mem_hierarchy_limit hδ.rankCriterion.2.2.1 hP hr.inclusion
  have hI' : IsForcingIterand N T (nameAction m Q) (nameAction m S) ∅ := by
    simpa only [nameAction_empty] using hr.iterand_nameAction hR hT he hI
  exact (retractedBaseTwoStepMap_translated_retraction hr hR hT ht hδ hP he hI).comp
    (normalizedTwoStepRetraction_spec hT (hr.top_of_mem ht hone) hδ.rankCriterion.2.2.1 hNδ hI')

theorem normalizedBaseTwoStepMap_prefix {P R N T one δ Q S m z : V}
    (hr : IsForcingRetraction N T P R m) (hR : IsForcingPreorder P R) (hT : IsForcingPreorder N T)
    (ht : IsForcingTop P R one) (hone : one ∈ N)
    (hδ : IsChoicelessInaccessible δ) (hP : P ∈ hierarchy δ)
    (he : ∀ p ∈ P, ⟨m ‘ p, p⟩ₖ ∈ R ∧ ⟨p, m ‘ p⟩ₖ ∈ R)
    (hI : IsForcingIterand P R Q S ∅) (hz : z ∈ boundedNameTwoStep P R δ Q) :
    kpair.π₁ ((normalizedBaseTwoStepMap P R N T one δ Q m) ‘ z) = m ‘ (kpair.π₁ z) := by
  let := hδ.1
  have hNδ := subset_mem_hierarchy_limit hδ.rankCriterion.2.2.1 hP hr.inclusion
  have hI' : IsForcingIterand N T (nameAction m Q) (nameAction m S) ∅ := by
    simpa only [nameAction_empty] using hr.iterand_nameAction hR hT he hI
  have hb := retractedBaseTwoStepMap_translated_retraction hr hR hT ht hδ hP he hI
  have hn := normalizedTwoStepRetraction_spec hT (hr.top_of_mem ht hone) hδ.rankCriterion.2.2.1 hNδ hI'
  rw [normalizedBaseTwoStepMap, value_compose_of_mem_function hb.maps hn.maps hz,
    normalizedTwoStepRetraction_prefix (function_value_mem hb.maps hz),
    retractedBaseTwoStepMap_value hz, retractedBaseTwoStepCode_prefix]

theorem normalizedBaseTwoStepMap_empty_tail {P R N T one δ Q S m p : V}
    (hr : IsForcingRetraction N T P R m) (hR : IsForcingPreorder P R) (hT : IsForcingPreorder N T)
    (ht : IsForcingTop P R one) (hone : one ∈ N)
    (hδ : IsChoicelessInaccessible δ) (hP : P ∈ hierarchy δ)
    (he : ∀ p ∈ P, ⟨m ‘ p, p⟩ₖ ∈ R ∧ ⟨p, m ‘ p⟩ₖ ∈ R)
    (hI : IsForcingIterand P R Q S ∅) (hp : p ∈ P) :
    (normalizedBaseTwoStepMap P R N T one δ Q m) ‘ ⟨p, ∅⟩ₖ = ⟨m ‘ p, ∅⟩ₖ := by
  let := hδ.1
  have hNδ := subset_mem_hierarchy_limit hδ.rankCriterion.2.2.1 hP hr.inclusion
  have hI' : IsForcingIterand N T (nameAction m Q) (nameAction m S) ∅ := by
    simpa only [nameAction_empty] using hr.iterand_nameAction hR hT he hI
  have htN := hr.top_of_mem ht hone
  have hb := retractedBaseTwoStepMap_translated_retraction hr hR hT ht hδ hP he hI
  have hn := normalizedTwoStepRetraction_spec hT htN hδ.rankCriterion.2.2.1 hNδ hI'
  have hroot := (pair_mem_boundedNameTwoStep _ _ _ _ _ _).mp (boundedNameTwoStep_top hR ht hP hI).1
  have hz : ⟨p, ∅⟩ₖ ∈ boundedNameTwoStep P R δ Q :=
    (pair_mem_boundedNameTwoStep _ _ _ _ _ _).mpr ⟨hp, hroot.2.1, empty_forcingName P,
      forcedTop_mem hR ht hp ⟨Q, hI.posetName⟩ ⟨S, hI.orderName⟩ ⟨∅, hI.topName⟩ (hI.top p hp)⟩
  have hrootN := (pair_mem_normalizedNameTwoStep _ _ _ _ _ _ _).mp (normalizedNameTwoStep_top hT htN hNδ hI').1
  have hzN : ⟨m ‘ p, ∅⟩ₖ ∈ normalizedNameTwoStep N T one δ (nameAction m Q) :=
    (pair_mem_normalizedNameTwoStep _ _ _ _ _ _ _).mpr ⟨function_value_mem hr.maps hp, hrootN.2⟩
  rw [normalizedBaseTwoStepMap, value_compose_of_mem_function hb.maps hn.maps hz,
    retractedBaseTwoStepMap_value hz, retractedBaseTwoStepCode_empty_tail, hn.fixes _ hzN]

theorem normalizedBaseTwoStepMap_equivalent {P R N T one δ Q S m z : V}
    (hr : IsForcingRetraction N T P R m) (hR : IsForcingPreorder P R) (hT : IsForcingPreorder N T)
    (ht : IsForcingTop P R one) (hone : one ∈ N)
    (hδ : IsChoicelessInaccessible δ) (hP : P ∈ hierarchy δ)
    (he : ∀ p ∈ P, ⟨m ‘ p, p⟩ₖ ∈ R ∧ ⟨p, m ‘ p⟩ₖ ∈ R)
    (hI : IsForcingIterand P R Q S ∅) (hz : z ∈ boundedNameTwoStep P R δ Q) :
    ⟨(normalizedBaseTwoStepMap P R N T one δ Q m) ‘ z, z⟩ₖ ∈
      nameTwoStepOrderOn P R S (boundedNameTwoStep P R δ Q) ∧
    ⟨z, (normalizedBaseTwoStepMap P R N T one δ Q m) ‘ z⟩ₖ ∈
      nameTwoStepOrderOn P R S (boundedNameTwoStep P R δ Q) := by
  let := hδ.1
  have hNδ := subset_mem_hierarchy_limit hδ.rankCriterion.2.2.1 hP hr.inclusion
  have hI' : IsForcingIterand N T (nameAction m Q) (nameAction m S) ∅ := by
    simpa only [nameAction_empty] using hr.iterand_nameAction hR hT he hI
  have htN := hr.top_of_mem ht hone
  have hb := retractedBaseTwoStepMap_translated_retraction hr hR hT ht hδ hP he hI
  have hn := normalizedTwoStepRetraction_spec hT htN hδ.rankCriterion.2.2.1 hNδ hI'
  have hbelow := hb.comp_below hn (boundedNameTwoStep_preorder hR ht hI.posetName hI.orderName hI.preorder)
    (fun w hw ↦ by
      rw [retractedBaseTwoStepMap_value hw]
      exact (retractedBaseTwoStepCode_equivalent hR ht hδ hP hr.inclusion hr.maps he hI hw).1)
    (normalizedTwoStepRetraction_below hT htN hδ.rankCriterion.2.2.1 hNδ hI') z hz
  have hc := normalizedBaseTwoStepMap_retraction hr hR hT ht hone hδ hP he hI
  have hnz := function_value_mem hc.maps hz
  exact ⟨hbelow, (hc.below z hz _ hnz).mpr
    ((normalizedNameTwoStep_preorder hT htN hI'.posetName hI'.orderName hI'.preorder).2.1 _ hnz)⟩

/-- Apply the successor comparison to the actual checked saturated collapse. -/
theorem saturatedWoodinPrefix_normalizedBase_retraction {P R N T one κ δ m : V}
    (hr : IsForcingRetraction N T P R m) (hR : IsForcingPreorder P R) (hT : IsForcingPreorder N T)
    (ht : IsForcingTop P R one) (hone : one ∈ N)
    (hδ : IsChoicelessInaccessible δ) (hP : P ∈ hierarchy δ) (hκδ : κ ⊆ δ)
    (he : ∀ p ∈ P, ⟨m ‘ p, p⟩ₖ ∈ R ∧ ⟨p, m ‘ p⟩ₖ ∈ R)
    (hκ : ∀ p ∈ P, p ∈ forcingFormula P R regularCardinalFormula (standardTuple ![checkName one κ])) :
    let Q := saturatedWoodinPrefixPosetName P R one κ δ
    let S := saturatedWoodinPrefixOrderName P R one κ δ
    IsForcingRetraction (normalizedNameTwoStep N T one δ (nameAction m Q))
      (nameTwoStepOrderOn N T (nameAction m S) (normalizedNameTwoStep N T one δ (nameAction m Q)))
      (twoStepConditions P R Q ∅) (twoStepOrder P R Q S ∅)
      (normalizedBaseTwoStepMap P R N T one δ Q m) := by
  dsimp only
  rw [saturatedWoodinPrefix_twoStep_eq_bounded hR hδ hP,
    saturatedWoodinPrefix_twoStepOrder_eq_bounded hR hδ hP]
  exact normalizedBaseTwoStepMap_retraction hr hR hT ht hone hδ hP he
    (saturatedWoodinPrefix_iterand hR ht hδ hP hκδ hκ)

end ZFVP
