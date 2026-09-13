import ZFVP.ModelTheory.InverseSourceCollapseCode
import ZFVP.ModelTheory.SaturatedCollapseRestoration

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- The selected ground cutoff restores dependent choice for the actual coded
stage, provided the saturation rank covers the original collapse subnames. -/
theorem forcingInverseSourceCollapseCode_restoration {θ s ζ γ δ : V} [IsOrdinal θ]
    (h : IsForcingIterationCode θ s) (h0 : ∅ ∈ θ)
    (hz : (∅ : V) ∈ forcingNameHierarchy (forcingInverseCodePoset θ s) ζ)
    (hγ : ∀ p ∈ forcingInverseCodePoset θ s,
      p ∈ forcingFormula (forcingInverseCodePoset θ s) (forcingInverseCodeOrder θ s)
        (regularCardinalFormula.or limitOfRegularCardinalsFormula)
        (standardTuple ![checkName (forcingInverseCodeTop θ s) γ]))
    (hDC : ∀ p ∈ forcingInverseCodePoset θ s,
      p ∈ forcingFormula (forcingInverseCodePoset θ s) (forcingInverseCodeOrder θ s)
        dependentChoiceAtFormula (standardTuple ![checkName (forcingInverseCodeTop θ s) γ]))
    (hδ : IsWoodinNamedPrefixCutoff (forcingInverseCodePoset θ s) (forcingInverseCodeOrder θ s)
      (forcingInverseCodeTop θ s) γ (forcingInverseHartogsName θ s γ) δ)
    (hU : domain (woodinCollapseName (forcingInverseCodePoset θ s) (forcingInverseCodeOrder θ s)
      (forcingInverseHartogsName θ s γ) (forcingInverseRestorationName θ s γ)) ⊆
        forcingNameHierarchy (forcingInverseCodePoset θ s) ζ) :
    let z := forcingInverseSourceCollapseCode θ s ζ γ
    γ ∈ forcingInverseSourceCutoff θ s γ ∧ IsChoicelessInaccessible (forcingInverseSourceCutoff θ s γ) ∧
      ∀ p ∈ (forcingCodeP z) ‘ θ,
        p ∈ forcingFormula ((forcingCodeP z) ‘ θ) ((forcingCodeR z) ‘ θ) dependentChoiceBelowFormula
          (standardTuple ![checkName ((forcingCodet z) ‘ θ) (forcingInverseSourceCutoff θ s γ)]) := by
  have c := h.system.inverseColumn h0 h.subset_universe
  have ht : IsForcingTop (forcingInverseCodePoset θ s) (forcingInverseCodeOrder θ s)
      (forcingInverseCodeTop θ s) := c.tops.top
  let τ : ForcingName (forcingInverseCodePoset θ s) :=
    ⟨checkName (forcingInverseCodeTop θ s) γ, checkName_isName ht.1 _⟩
  let κ : ForcingName (forcingInverseCodePoset θ s) :=
    ⟨forcingInverseHartogsName θ s γ, hartogsNumberName_isName _ _ _⟩
  have hk : ∀ p ∈ forcingInverseCodePoset θ s,
      p ∈ forcingFormula (forcingInverseCodePoset θ s) (forcingInverseCodeOrder θ s)
        regularCardinalFormula (standardTuple ![κ.val]) :=
    fun p hp ↦ hartogsNumberName_forces_regular c.order.preorder ht hp τ (hγ p hp) (hDC p hp)
  have hd := (forcingInverseSourceCutoff_spec hδ).2.1
  have hr := (woodinNamedPrefixCutoff_iff_saturated_forces c.order.preorder ht κ hz hU hk).mp hd
  dsimp only
  refine ⟨hr.1, hr.2.1, ?_⟩
  simpa only [forcingInverseSourceCollapseCode, forcingInverseCollapseCode, forcingInverseTwoStepCode,
    forcingTwoStepColumnCode, forcingIterationCodeNext, forcingCodeP_code, forcingCodeR_code,
    forcingCodet_code, forcingFamilyNext_new, forcingInverseCollapseName, forcingInverseRestorationName,
    forcingInverseCodePoset, forcingInverseCodeOrder, forcingInverseCodeTop, κ] using hr.2.2

end ZFVP
