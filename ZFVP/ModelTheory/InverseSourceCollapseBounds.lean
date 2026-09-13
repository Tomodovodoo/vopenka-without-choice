import ZFVP.ModelTheory.InverseSourceCollapseCode
import ZFVP.ModelTheory.ForcingHartogsChoice

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def forcingInverseSourceCollapseBoundTable (θ s ζ γ B i I : V) : V :=
  forcingInverseCollapseBoundTable θ s ζ (forcingInverseHartogsName θ s γ)
    (forcingInverseRestorationName θ s γ) B i I

theorem forcingInverseSourceCollapseCode_bound_table {θ s ζ γ B i I : V}
    [IsOrdinal θ] [IsOrdinal ζ] [IsOrdinal γ]
    (h : IsForcingIterationCode θ s) (h0 : ∅ ∈ θ) (hi : i ∈ θ)
    (hz : (∅ : V) ∈ forcingNameHierarchy (forcingInverseCodePoset θ s) ζ)
    (hIζ : I ∈ internalCofinality ζ) (hIγ : I ∈ γ)
    (hγ : ∀ p ∈ forcingInverseCodePoset θ s,
      p ∈ forcingFormula (forcingInverseCodePoset θ s) (forcingInverseCodeOrder θ s)
        (regularCardinalFormula.or limitOfRegularCardinalsFormula)
        (standardTuple ![checkName (forcingInverseCodeTop θ s) γ]))
    (hDC : ∀ p ∈ forcingInverseCodePoset θ s,
      p ∈ forcingFormula (forcingInverseCodePoset θ s) (forcingInverseCodeOrder θ s)
        dependentChoiceAtFormula (standardTuple ![checkName (forcingInverseCodeTop θ s) γ]))
    (hb : IsCoherentForcingBound θ (forcingCodeP s) (forcingCodeR s) (forcingCodeπ s) B i I)
    (hc : IsSectionCompatibleForcingBound θ (forcingCodeP s) (forcingCodeR s) (forcingCodeπ s)
      (forcingCodeE s) B i I) :
    let z := forcingInverseSourceCollapseCode θ s ζ γ
    let B' := forcingInverseSourceCollapseBoundTable θ s ζ γ B i I
    IsCoherentForcingBound (succ θ) (forcingCodeP z) (forcingCodeR z) (forcingCodeπ z) B' i I ∧
      IsSectionCompatibleForcingBound (succ θ) (forcingCodeP z) (forcingCodeR z) (forcingCodeπ z)
        (forcingCodeE z) B' i I := by
  have c := h.system.inverseColumn h0 h.subset_universe
  have ht : IsForcingTop (forcingInverseCodePoset θ s) (forcingInverseCodeOrder θ s)
      (forcingInverseCodeTop θ s) := c.tops.top
  let τ : ForcingName (forcingInverseCodePoset θ s) :=
    ⟨checkName (forcingInverseCodeTop θ s) γ, checkName_isName ht.1 _⟩
  let κ : ForcingName (forcingInverseCodePoset θ s) :=
    ⟨forcingInverseHartogsName θ s γ, hartogsNumberName_isName _ _ _⟩
  let δ : ForcingName (forcingInverseCodePoset θ s) :=
    ⟨forcingInverseRestorationName θ s γ, checkName_isName ht.1 _⟩
  exact forcingInverseCollapseCode_bound_table h h0 hi κ δ hz hIζ
    (fun p hp ↦ hartogsNumberName_forces_regular c.order.preorder ht hp τ (hγ p hp) (hDC p hp))
    (fun _ hp ↦ forces_checked_ordinal c.order.preorder ht inferInstance hp)
    (fun p hp ↦ (hartogsNumberName_checked_lower_choice c.order.preorder ht hp hIγ (hDC p hp)).1)
    (fun p hp ↦ (hartogsNumberName_checked_lower_choice c.order.preorder ht hp hIγ (hDC p hp)).2)
    hb hc

end ZFVP
