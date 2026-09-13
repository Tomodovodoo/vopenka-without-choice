import ZFVP.ModelTheory.WoodinInverseSourceCutoff
import ZFVP.ModelTheory.SaturatedHartogsPreservation

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem IsWoodinIteration.inverse_sourceStage {δ θ s K : V} [IsOrdinal θ]
    (h : IsWoodinIteration δ θ s K) (hδ : IsWoodinSupercompact δ) (hθ : θ ∈ δ) (h0 : ∅ ∈ θ)
    (hlim : ∀ i ∈ θ, succ i ∈ θ)
    (hγ : ∀ p ∈ forcingInverseCodePoset θ s,
      p ∈ forcingFormula (forcingInverseCodePoset θ s) (forcingInverseCodeOrder θ s)
        (regularCardinalFormula.or limitOfRegularCardinalsFormula)
        (standardTuple ![checkName (forcingInverseCodeTop θ s) (woodinLimitCardinal K)]))
    (hDC : ∀ p ∈ forcingInverseCodePoset θ s,
      p ∈ forcingFormula (forcingInverseCodePoset θ s) (forcingInverseCodeOrder θ s)
        dependentChoiceAtFormula (standardTuple ![checkName (forcingInverseCodeTop θ s) (woodinLimitCardinal K)])) :
    let c := forcingInverseSourceCutoff θ s (woodinLimitCardinal K)
    let z := forcingInverseSourceCollapseCode θ s c (woodinLimitCardinal K)
    c ∈ δ ∧ woodinLimitCardinal K ∈ c ∧ IsChoicelessInaccessible c ∧
      IsForcingIterationCode (succ θ) z ∧ ForcingCodeExtends s z ∧
      ∀ p ∈ (forcingCodeP z) ‘ θ,
        p ∈ forcingFormula ((forcingCodeP z) ‘ θ) ((forcingCodeR z) ‘ θ) woodinStageCardinalFormula
          (standardTuple ![checkName ((forcingCodet z) ‘ θ) c]) := by
  obtain ⟨hcδ, hc⟩ := h.inverse_sourceCutoff hδ hθ h0 hγ hDC
  have hs := h.inverse_small_above_limit hlim hc.2.1 hc.1
  have col := h.code.system.inverseColumn h0 h.code.subset_universe
  have ht : IsForcingTop (forcingInverseCodePoset θ s) (forcingInverseCodeOrder θ s)
      (forcingInverseCodeTop θ s) := col.tops.top
  let τ : ForcingName (forcingInverseCodePoset θ s) :=
    ⟨checkName (forcingInverseCodeTop θ s) (woodinLimitCardinal K), checkName_isName ht.1 _⟩
  have hk : ∀ p ∈ forcingInverseCodePoset θ s,
      p ∈ forcingFormula (forcingInverseCodePoset θ s) (forcingInverseCodeOrder θ s)
        regularCardinalFormula (standardTuple ![forcingInverseHartogsName θ s (woodinLimitCardinal K)]) :=
    fun p hp ↦ hartogsNumberName_forces_regular col.order.preorder ht hp τ (hγ p hp) (hDC p hp)
  have hz : (∅ : V) ∈ forcingNameHierarchy (forcingInverseCodePoset θ s)
      (forcingInverseSourceCutoff θ s (woodinLimitCardinal K)) :=
    (mem_forcingNameHierarchy _ _ _).mpr ⟨∅, hc.2.1.regular.2.1 ∅ (by simp), by simp⟩
  have hp := saturatedHartogsSuccessor_forces_cardinal col.order.preorder ht hk hc hs.1
  dsimp only
  refine ⟨hcδ, hc.1, hc.2.1, forcingInverseSourceCollapseCode_valid h.code h0 hz hγ hDC,
    forcingInverseSourceCollapseCode_extends h.code _ _, ?_⟩
  simpa only [forcingInverseSourceCollapseCode, forcingInverseCollapseCode, forcingInverseTwoStepCode,
    forcingTwoStepColumnCode, forcingIterationCodeNext, forcingCodeP_code, forcingCodeR_code,
    forcingCodet_code, forcingFamilyNext_new, forcingInverseCollapseName, forcingInverseRestorationName,
    forcingInverseCodePoset, forcingInverseCodeOrder, forcingInverseCodeTop, forcingInverseHartogsName,
    saturatedHartogsPosetName, saturatedHartogsOrderName] using hp

end ZFVP
