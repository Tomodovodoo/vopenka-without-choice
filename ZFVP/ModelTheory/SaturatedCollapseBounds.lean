import ZFVP.ModelTheory.SaturatedEmptyIterand
import ZFVP.ModelTheory.SaturatedTwoStepTransfer
import ZFVP.ModelTheory.WoodinCollapseUnionName

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def saturatedWoodinCollapseName (P R ζ κ δ : V) : V :=
  forcingSaturatedName P R (forcingNameHierarchy P ζ) (woodinCollapseName P R κ δ)

theorem saturatedWoodinCollapse_union_bound {P R one ζ I p f : V} [IsOrdinal ζ]
    (hR : IsForcingPreorder P R) (htop : IsForcingTop P R one)
    (κ δ : ForcingName P) (hI : I ∈ internalCofinality ζ)
    (hzero : (∅ : V) ∈ forcingNameHierarchy P ζ) (hp : p ∈ P)
    (hκ : p ∈ forcingFormula P R regularCardinalFormula (standardTuple ![κ.val]))
    (hδ : p ∈ forcingFormula P R IsOrdinal.dfn (standardTuple ![δ.val]))
    (hDC : p ∈ forcingFormula P R dependentChoiceAtFormula (standardTuple ![checkName one I]))
    (hIκ : p ∈ forcingFormula P R nameMemberFormula (standardTuple ![checkName one I, κ.val]))
    (hf : IsForcingDirectedFamily
      (twoStepConditions P R (saturatedWoodinCollapseName P R ζ κ.val δ.val) ∅)
      (twoStepOrder P R (saturatedWoodinCollapseName P R ζ κ.val δ.val)
        (reverseInclusionOrderName P R (saturatedWoodinCollapseName P R ζ κ.val δ.val)) ∅) I f)
    (hpbelow : ∀ a ∈ I, ⟨p, kpair.π₁ (f ‘ a)⟩ₖ ∈ R) :
    twoStepUnionBound I p f ∈ twoStepConditions P R (saturatedWoodinCollapseName P R ζ κ.val δ.val) ∅ ∧
      ∀ a ∈ I, ⟨twoStepUnionBound I p f, f ‘ a⟩ₖ ∈
        twoStepOrder P R (saturatedWoodinCollapseName P R ζ κ.val δ.val)
          (reverseInclusionOrderName P R (saturatedWoodinCollapseName P R ζ κ.val δ.val)) ∅ := by
  let Q : ForcingName P := ⟨woodinCollapseName P R κ.val δ.val, woodinCollapseName_isName _ _ _ _⟩
  let N : ForcingName P := ⟨saturatedWoodinCollapseName P R ζ κ.val δ.val,
    forcingSaturatedName_isName _ _ _ _⟩
  let S : ForcingName P := ⟨reverseInclusionOrderName P R N.val, reverseInclusionOrderName_isName _ _ _⟩
  exact saturated_twoStep_union_bound hR htop Q S hI hzero hp
    (woodinCollapseName_forces_unionClosedAt hR htop hp κ δ
      ⟨checkName one I, checkName_isName htop.1 _⟩ hκ hδ hDC hIκ)
    (reverseInclusionOrderName_forces hR htop hp N) hf hpbelow

end ZFVP
