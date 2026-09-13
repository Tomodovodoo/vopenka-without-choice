import ZFVP.ModelTheory.NormalizedTwoStepModel
import ZFVP.ModelTheory.NormalizedWoodinPrefix
import ZFVP.ModelTheory.ForcingContextCongruence
import ZFVP.ModelTheory.TwoStepQuotient

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable {P R one κ δ : V}

local notation "Q" => saturatedWoodinPrefixPosetName P R one κ δ
local notation "S" => saturatedWoodinPrefixOrderName P R one κ δ
local notation "C" => twoStepConditions P R Q ∅
local notation "T" => twoStepOrder P R Q S ∅

noncomputable def normalizedWoodinPrefixContext
    (hR : IsForcingPreorder P R) (ht : IsForcingTop P R one)
    (hδ : IsChoicelessInaccessible δ) (hP : P ∈ hierarchy δ) (hκδ : κ ⊆ δ)
    (hκ : ∀ p ∈ P, p ∈ forcingFormula P R regularCardinalFormula (standardTuple ![checkName one κ]))
    (G : Set V) (hG : IsExternalForcingGeneric C T G) : ForcingContext V := by
  let := hδ.1
  have hb : IsExternalForcingGeneric (boundedNameTwoStep P R δ Q)
      (nameTwoStepOrderOn P R S (boundedNameTwoStep P R δ Q)) G := by
    rwa [saturatedWoodinPrefix_twoStep_eq_bounded hR hδ hP,
      saturatedWoodinPrefix_twoStepOrder_eq_bounded hR hδ hP] at hG
  exact normalizedTwoStepContext hR ht hδ.rankCriterion.2.2.1 hP
    (saturatedWoodinPrefix_iterand hR ht hδ hP hκδ hκ) G hb

variable (hR : IsForcingPreorder P R) (ht : IsForcingTop P R one)
  (hδ : IsChoicelessInaccessible δ) (hP : P ∈ hierarchy δ) (hκδ : κ ⊆ δ)
  (hκ : ∀ p ∈ P, p ∈ forcingFormula P R regularCardinalFormula (standardTuple ![checkName one κ]))
  (G : Set V)

noncomputable def normalizedWoodinPrefixModelEquiv (hG : IsExternalForcingGeneric C T G) :
    (normalizedWoodinPrefixContext hR ht hδ hP hκδ hκ G hG).Model ≃
      (twoStepTotalContext hR ht (saturatedWoodinPrefix_iterand hR ht hδ hP hκδ hκ) hG).Model := by
  let := hδ.1
  let hI := saturatedWoodinPrefix_iterand hR ht hδ hP hκδ hκ
  have hb : IsExternalForcingGeneric (boundedNameTwoStep P R δ Q)
      (nameTwoStepOrderOn P R S (boundedNameTwoStep P R δ Q)) G := by
    rwa [saturatedWoodinPrefix_twoStep_eq_bounded hR hδ hP,
      saturatedWoodinPrefix_twoStepOrder_eq_bounded hR hδ hP] at hG
  let B := boundedTwoStepContext hR ht hP hI G hb
  let D := twoStepTotalContext hR ht hI hG
  have he : B = D := ForcingContext.eq_of_data_eq B D
    (saturatedWoodinPrefix_twoStep_eq_bounded hR hδ hP).symm
    (saturatedWoodinPrefix_twoStepOrder_eq_bounded hR hδ hP).symm rfl rfl
  exact (normalizedTwoStepModelEquiv hR ht hδ.rankCriterion.2.2.1 hP hI G hb).trans
    (ForcingContext.modelCongr he)

theorem normalizedWoodinPrefixModelEquiv_mem_iff (hG : IsExternalForcingGeneric C T G)
    (x y : (normalizedWoodinPrefixContext hR ht hδ hP hκδ hκ G hG).Model) :
    normalizedWoodinPrefixModelEquiv hR ht hδ hP hκδ hκ G hG x ∈
      normalizedWoodinPrefixModelEquiv hR ht hδ hP hκδ hκ G hG y ↔ x ∈ y := by
  let := hδ.1
  unfold normalizedWoodinPrefixContext at x y ⊢
  simp only [normalizedWoodinPrefixModelEquiv, Equiv.trans_apply,
    ForcingContext.modelCongr_mem_iff, normalizedTwoStepModelEquiv_mem_iff]

theorem normalizedWoodinPrefixModelEquiv_check (hG : IsExternalForcingGeneric C T G) (x : V) :
    normalizedWoodinPrefixModelEquiv hR ht hδ hP hκδ hκ G hG
      ((normalizedWoodinPrefixContext hR ht hδ hP hκδ hκ G hG).check x) =
    (twoStepTotalContext hR ht (saturatedWoodinPrefix_iterand hR ht hδ hP hκδ hκ) hG).check x := by
  let := hδ.1
  unfold normalizedWoodinPrefixContext
  simp only [normalizedWoodinPrefixModelEquiv, Equiv.trans_apply,
    normalizedTwoStepModelEquiv_check, ForcingContext.modelCongr_check]

noncomputable def normalizedWoodinPrefixElementaryMap (hG : IsExternalForcingGeneric C T G) :
    ElementaryMap (normalizedWoodinPrefixContext hR ht hδ hP hκδ hκ G hG).Model
      (twoStepTotalContext hR ht (saturatedWoodinPrefix_iterand hR ht hδ hP hκδ hκ) hG).Model :=
  ElementaryMap.ofMembershipIso (normalizedWoodinPrefixModelEquiv hR ht hδ hP hκδ hκ G hG)
    (normalizedWoodinPrefixModelEquiv_mem_iff hR ht hδ hP hκδ hκ G hG)

end ZFVP
