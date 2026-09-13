import ZFVP.ModelTheory.BoundedSaturatedTwoStep
import ZFVP.ModelTheory.NormalizedTwoStepForcing
import ZFVP.ModelTheory.SaturatedWoodinIterand

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable {P R one κ δ : V}

local notation "Q" => (saturatedWoodinPrefixPosetName P R one κ δ)
local notation "S" => (saturatedWoodinPrefixOrderName P R one κ δ)

theorem saturatedWoodinPrefix_twoStep_eq_bounded
    (hR : IsForcingPreorder P R) (hδ : IsChoicelessInaccessible δ) (hP : P ∈ hierarchy δ) :
    twoStepConditions P R Q ∅ = boundedNameTwoStep P R δ Q :=
  saturatedTwoStep_eq_boundedNameTwoStep hR hδ hP

theorem saturatedWoodinPrefix_twoStepOrder_eq_bounded
    (hR : IsForcingPreorder P R) (hδ : IsChoicelessInaccessible δ) (hP : P ∈ hierarchy δ) :
    twoStepOrder P R Q S ∅ = nameTwoStepOrderOn P R S (boundedNameTwoStep P R δ Q) :=
  saturatedTwoStepOrder_eq_nameTwoStepOrderOn hR hδ hP

theorem saturatedWoodinPrefix_normalized_map
    (hR : IsForcingPreorder P R) (ht : IsForcingTop P R one)
    (hδ : IsChoicelessInaccessible δ) (hP : P ∈ hierarchy δ) (hκδ : κ ⊆ δ)
    (hκ : ∀ p ∈ P, p ∈ forcingFormula P R regularCardinalFormula (standardTuple ![checkName one κ])) :
    guardedTwoStepMap P R one δ Q ∈ normalizedNameTwoStep P R one δ Q ^ twoStepConditions P R Q ∅ := by
  let := hδ.1
  have hi := saturatedWoodinPrefix_iterand hR ht hδ hP hκδ hκ
  have h0 := forcedTop_mem hR ht ht.1 ⟨Q, hi.posetName⟩ ⟨S, hi.orderName⟩ ⟨∅, hi.topName⟩ (hi.top one ht.1)
  rw [saturatedWoodinPrefix_twoStep_eq_bounded hR hδ hP]
  exact guardedTwoStepMap_function hR ht hδ.rankCriterion.2.2.1 hP h0

theorem saturatedWoodinPrefix_normalized_order_iff {z w : V}
    (hR : IsForcingPreorder P R) (ht : IsForcingTop P R one)
    (hδ : IsChoicelessInaccessible δ) (hP : P ∈ hierarchy δ) (hκδ : κ ⊆ δ)
    (hκ : ∀ p ∈ P, p ∈ forcingFormula P R regularCardinalFormula (standardTuple ![checkName one κ]))
    (hz : z ∈ twoStepConditions P R Q ∅) (hw : w ∈ twoStepConditions P R Q ∅) :
    ⟨guardedTwoStepCode P R one z, guardedTwoStepCode P R one w⟩ₖ ∈
      nameTwoStepOrderOn P R S (normalizedNameTwoStep P R one δ Q) ↔
    ⟨z, w⟩ₖ ∈ twoStepOrder P R Q S ∅ := by
  let := hδ.1
  have hi := saturatedWoodinPrefix_iterand hR ht hδ hP hκδ hκ
  have h0 := forcedTop_mem hR ht ht.1 ⟨Q, hi.posetName⟩ ⟨S, hi.orderName⟩ ⟨∅, hi.topName⟩ (hi.top one ht.1)
  rw [saturatedWoodinPrefix_twoStep_eq_bounded hR hδ hP] at hz hw
  rw [saturatedWoodinPrefix_twoStepOrder_eq_bounded hR hδ hP]
  exact guardedTwoStepCode_order_iff hR ht hδ.rankCriterion.2.2.1 hP h0 hz hw

theorem saturatedWoodinPrefix_normalized_generic_iff {G : Set V}
    (hR : IsForcingPreorder P R) (ht : IsForcingTop P R one)
    (hδ : IsChoicelessInaccessible δ) (hP : P ∈ hierarchy δ) (hκδ : κ ⊆ δ)
    (hκ : ∀ p ∈ P, p ∈ forcingFormula P R regularCardinalFormula (standardTuple ![checkName one κ]))
    (hG : IsExternalForcingFilter (twoStepConditions P R Q ∅) (twoStepOrder P R Q S ∅) G) :
    IsExternalForcingGeneric (twoStepConditions P R Q ∅) (twoStepOrder P R Q S ∅) G ↔
    IsExternalForcingGeneric (normalizedNameTwoStep P R one δ Q)
      (nameTwoStepOrderOn P R S (normalizedNameTwoStep P R one δ Q))
      {z | z ∈ G ∧ z ∈ normalizedNameTwoStep P R one δ Q} := by
  let := hδ.1
  have hi := saturatedWoodinPrefix_iterand hR ht hδ hP hκδ hκ
  have h0 := forcedTop_mem hR ht ht.1 ⟨Q, hi.posetName⟩ ⟨S, hi.orderName⟩ ⟨∅, hi.topName⟩ (hi.top one ht.1)
  rw [saturatedWoodinPrefix_twoStep_eq_bounded hR hδ hP,
    saturatedWoodinPrefix_twoStepOrder_eq_bounded hR hδ hP] at hG ⊢
  exact normalizedNameTwoStep_generic_iff hR ht hδ.rankCriterion.2.2.1 hP
    hi.posetName hi.orderName h0 hi.preorder hG

end ZFVP
