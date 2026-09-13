import ZFVP.ModelTheory.InverseTwoStepCode
import ZFVP.ModelTheory.SaturatedCollapseBounds

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def forcingInverseCodePoset (θ s : V) : V :=
  forcingInverseLimit θ (forcingCodeP s) (forcingCodeπ s) (forcingCodeUniverse s)

noncomputable def forcingInverseCodeOrder (θ s : V) : V :=
  forcingThreadOrder θ (forcingCodeR s) (forcingInverseCodePoset θ s)

noncomputable def forcingInverseCodeTop (θ s : V) : V :=
  forcingSectionThread θ (forcingCodeπ s) (forcingCodeE s) ∅ ((forcingCodet s) ‘ ∅)

noncomputable def forcingInverseCollapseName (θ s ζ κ δ : V) : V :=
  saturatedWoodinCollapseName (forcingInverseCodePoset θ s) (forcingInverseCodeOrder θ s) ζ κ δ

noncomputable def forcingInverseCollapseCode (θ s ζ κ δ : V) : V :=
  let Q := forcingInverseCollapseName θ s ζ κ δ
  forcingInverseTwoStepCode θ s Q
    (reverseInclusionOrderName (forcingInverseCodePoset θ s) (forcingInverseCodeOrder θ s) Q) ∅

theorem forcingInverseCollapse_iterand {θ s ζ : V} [IsOrdinal θ]
    (h : IsForcingIterationCode θ s) (h0 : ∅ ∈ θ)
    (κ δ : ForcingName (forcingInverseCodePoset θ s))
    (hz : (∅ : V) ∈ forcingNameHierarchy (forcingInverseCodePoset θ s) ζ)
    (hκ : ∀ p ∈ forcingInverseCodePoset θ s,
      p ∈ forcingFormula (forcingInverseCodePoset θ s) (forcingInverseCodeOrder θ s)
        regularCardinalFormula (standardTuple ![κ.val]))
    (hδ : ∀ p ∈ forcingInverseCodePoset θ s,
      p ∈ forcingFormula (forcingInverseCodePoset θ s) (forcingInverseCodeOrder θ s)
        IsOrdinal.dfn (standardTuple ![δ.val])) :
    IsForcingIterand (forcingInverseCodePoset θ s) (forcingInverseCodeOrder θ s)
      (forcingInverseCollapseName θ s ζ κ.val δ.val)
      (reverseInclusionOrderName (forcingInverseCodePoset θ s) (forcingInverseCodeOrder θ s)
        (forcingInverseCollapseName θ s ζ κ.val δ.val)) ∅ := by
  have c := h.system.inverseColumn h0 h.subset_universe
  exact saturatedWoodinCollapse_empty_iterand c.order.preorder c.tops.top κ δ hz hκ hδ

theorem forcingInverseCollapseCode_valid {θ s ζ : V} [IsOrdinal θ]
    (h : IsForcingIterationCode θ s) (h0 : ∅ ∈ θ)
    (κ δ : ForcingName (forcingInverseCodePoset θ s))
    (hz : (∅ : V) ∈ forcingNameHierarchy (forcingInverseCodePoset θ s) ζ)
    (hκ : ∀ p ∈ forcingInverseCodePoset θ s,
      p ∈ forcingFormula (forcingInverseCodePoset θ s) (forcingInverseCodeOrder θ s)
        regularCardinalFormula (standardTuple ![κ.val]))
    (hδ : ∀ p ∈ forcingInverseCodePoset θ s,
      p ∈ forcingFormula (forcingInverseCodePoset θ s) (forcingInverseCodeOrder θ s)
        IsOrdinal.dfn (standardTuple ![δ.val])) :
    IsForcingIterationCode (succ θ) (forcingInverseCollapseCode θ s ζ κ.val δ.val) :=
  forcingInverseTwoStepCode_valid h h0 (forcingInverseCollapse_iterand h h0 κ δ hz hκ hδ)

theorem forcingInverseCollapseCode_extends {θ s : V} (h : IsForcingIterationCode θ s) (ζ κ δ : V) :
    ForcingCodeExtends s (forcingInverseCollapseCode θ s ζ κ δ) :=
  forcingInverseTwoStepCode_extends h _ _ _

noncomputable def forcingInverseCollapseBoundTable (θ s ζ κ δ B i I : V) : V :=
  forcingInverseTwoStepBoundTable θ s B i I (forcingInverseCollapseName θ s ζ κ δ) ∅

theorem forcingInverseCollapseCode_bound_table {θ s ζ B i I : V} [IsOrdinal θ] [IsOrdinal ζ]
    (h : IsForcingIterationCode θ s) (h0 : ∅ ∈ θ) (hi : i ∈ θ)
    (κ δ : ForcingName (forcingInverseCodePoset θ s))
    (hz : (∅ : V) ∈ forcingNameHierarchy (forcingInverseCodePoset θ s) ζ)
    (hI : I ∈ internalCofinality ζ)
    (hκ : ∀ p ∈ forcingInverseCodePoset θ s,
      p ∈ forcingFormula (forcingInverseCodePoset θ s) (forcingInverseCodeOrder θ s)
        regularCardinalFormula (standardTuple ![κ.val]))
    (hδ : ∀ p ∈ forcingInverseCodePoset θ s,
      p ∈ forcingFormula (forcingInverseCodePoset θ s) (forcingInverseCodeOrder θ s)
        IsOrdinal.dfn (standardTuple ![δ.val]))
    (hDC : ∀ p ∈ forcingInverseCodePoset θ s,
      p ∈ forcingFormula (forcingInverseCodePoset θ s) (forcingInverseCodeOrder θ s)
        dependentChoiceAtFormula (standardTuple ![checkName (forcingInverseCodeTop θ s) I]))
    (hIκ : ∀ p ∈ forcingInverseCodePoset θ s,
      p ∈ forcingFormula (forcingInverseCodePoset θ s) (forcingInverseCodeOrder θ s)
        nameMemberFormula (standardTuple ![checkName (forcingInverseCodeTop θ s) I, κ.val]))
    (hb : IsCoherentForcingBound θ (forcingCodeP s) (forcingCodeR s) (forcingCodeπ s) B i I)
    (hc : IsSectionCompatibleForcingBound θ (forcingCodeP s) (forcingCodeR s) (forcingCodeπ s)
      (forcingCodeE s) B i I) :
    let z := forcingInverseCollapseCode θ s ζ κ.val δ.val
    let B' := forcingInverseCollapseBoundTable θ s ζ κ.val δ.val B i I
    IsCoherentForcingBound (succ θ) (forcingCodeP z) (forcingCodeR z) (forcingCodeπ z) B' i I ∧
      IsSectionCompatibleForcingBound (succ θ) (forcingCodeP z) (forcingCodeR z) (forcingCodeπ z)
        (forcingCodeE z) B' i I := by
  apply forcingInverseTwoStepCode_bound_table h h0 hi hb hc
    (forcingInverseCollapse_iterand h h0 κ δ hz hκ hδ)
  dsimp only
  intro f hf q hq hbelow
  have c := h.system.inverseColumn h0 h.subset_universe
  exact saturatedWoodinCollapse_union_bound c.order.preorder c.tops.top κ δ hI hz hq
    (hκ q hq) (hδ q hq) (hDC q hq) (hIκ q hq) hf hbelow

end ZFVP


