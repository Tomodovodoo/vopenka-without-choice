import ZFVP.ModelTheory.InverseCollapseCode
import ZFVP.ModelTheory.ForcingHartogsRegular
import ZFVP.SetTheory.WoodinNamedPrefixCutoff
import ZFVP.ModelTheory.ForcingCheckedBounded

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def forcingInverseHartogsName (θ s γ : V) : V :=
  hartogsNumberName (forcingInverseCodePoset θ s) (forcingInverseCodeOrder θ s)
    (checkName (forcingInverseCodeTop θ s) γ)

noncomputable def forcingInverseSourceCutoff (θ s γ : V) : V :=
  woodinNamedPrefixCutoff (forcingInverseCodePoset θ s) (forcingInverseCodeOrder θ s)
    (forcingInverseCodeTop θ s) γ (forcingInverseHartogsName θ s γ)

instance forcingInverseSourceCutoff_ordinal (θ s γ : V) : IsOrdinal (forcingInverseSourceCutoff θ s γ) :=
  woodinNamedPrefixCutoff_ordinal _ _ _ _ _

noncomputable def forcingInverseRestorationName (θ s γ : V) : V :=
  checkName (forcingInverseCodeTop θ s) (forcingInverseSourceCutoff θ s γ)

noncomputable def forcingInverseSourceCollapseCode (θ s ζ γ : V) : V :=
  forcingInverseCollapseCode θ s ζ (forcingInverseHartogsName θ s γ)
    (forcingInverseRestorationName θ s γ)

/-- The collapse cardinal is computed in the extension, while its upper cutoff
is selected in the ground model. A cutoff witness is needed for restoration. -/
theorem forcingInverseSourceCollapseCode_valid {θ s ζ γ : V} [IsOrdinal θ]
    (h : IsForcingIterationCode θ s) (h0 : ∅ ∈ θ)
    (hz : (∅ : V) ∈ forcingNameHierarchy (forcingInverseCodePoset θ s) ζ)
    (hγ : ∀ p ∈ forcingInverseCodePoset θ s,
      p ∈ forcingFormula (forcingInverseCodePoset θ s) (forcingInverseCodeOrder θ s)
        (regularCardinalFormula.or limitOfRegularCardinalsFormula)
        (standardTuple ![checkName (forcingInverseCodeTop θ s) γ]))
    (hDC : ∀ p ∈ forcingInverseCodePoset θ s,
      p ∈ forcingFormula (forcingInverseCodePoset θ s) (forcingInverseCodeOrder θ s)
        dependentChoiceAtFormula (standardTuple ![checkName (forcingInverseCodeTop θ s) γ])) :
    IsForcingIterationCode (succ θ) (forcingInverseSourceCollapseCode θ s ζ γ) := by
  have c := h.system.inverseColumn h0 h.subset_universe
  have ht : IsForcingTop (forcingInverseCodePoset θ s) (forcingInverseCodeOrder θ s)
      (forcingInverseCodeTop θ s) := c.tops.top
  let τ : ForcingName (forcingInverseCodePoset θ s) :=
    ⟨checkName (forcingInverseCodeTop θ s) γ, checkName_isName ht.1 _⟩
  let κ : ForcingName (forcingInverseCodePoset θ s) :=
    ⟨forcingInverseHartogsName θ s γ, hartogsNumberName_isName _ _ _⟩
  let δ : ForcingName (forcingInverseCodePoset θ s) :=
    ⟨forcingInverseRestorationName θ s γ, checkName_isName ht.1 _⟩
  exact forcingInverseCollapseCode_valid h h0 κ δ hz
    (fun p hp ↦ hartogsNumberName_forces_regular c.order.preorder ht hp τ (hγ p hp) (hDC p hp))
    (fun _ hp ↦ forces_checked_ordinal c.order.preorder ht inferInstance hp)

theorem forcingInverseSourceCutoff_spec {θ s γ δ : V}
    (hδ : IsWoodinNamedPrefixCutoff (forcingInverseCodePoset θ s) (forcingInverseCodeOrder θ s)
      (forcingInverseCodeTop θ s) γ (forcingInverseHartogsName θ s γ) δ) :
    IsLeastOrdinal (IsWoodinNamedPrefixCutoff (forcingInverseCodePoset θ s) (forcingInverseCodeOrder θ s)
      (forcingInverseCodeTop θ s) γ (forcingInverseHartogsName θ s γ)) (forcingInverseSourceCutoff θ s γ) :=
  woodinNamedPrefixCutoff_spec hδ

theorem forcingInverseSourceCollapseCode_extends {θ s : V} (h : IsForcingIterationCode θ s)
    (ζ γ : V) : ForcingCodeExtends s (forcingInverseSourceCollapseCode θ s ζ γ) :=
  forcingInverseCollapseCode_extends h _ _ _

end ZFVP
