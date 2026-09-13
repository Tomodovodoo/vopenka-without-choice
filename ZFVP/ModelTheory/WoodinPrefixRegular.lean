import ZFVP.ModelTheory.WoodinPrefixSuccessor
import ZFVP.ModelTheory.WoodinCollapseCutoffRegular
import ZFVP.ModelTheory.ForcingSmallInaccessible
import ZFVP.ModelTheory.ForcingCheckedTruth

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem ForcingContext.check_regular_of_collapse (B : ForcingContext V) {κ δ : V}
    (hκ : IsRegularCardinal κ) (hδ : IsChoicelessInaccessible δ) (hκδ : κ ∈ δ)
    (hP : B.P = woodinCollapse κ δ) (hR : B.R = woodinCollapseOrder κ δ)
    (ho : B.one = ∅) : IsRegularCardinal (B.check δ) := by
  have hG : IsExternalForcingGeneric (woodinCollapse κ δ) (woodinCollapseOrder κ δ) B.G := by
    rw [← hP, ← hR]
    exact B.generic
  have he : B = woodinCollapseContext hκ δ B.G hG := by
    cases B
    cases hP
    cases hR
    cases ho
    rfl
  exact he ▸ WoodinCollapseModel.check_cutoff_regular hκ hδ hκδ hG

theorem woodinPrefixSuccessor_regular {P R one κ δ : V}
    (hR : IsForcingPreorder P R) (htop : IsForcingTop P R one)
    (hκ : ∀ p ∈ P, p ∈ forcingFormula P R regularCardinalFormula (standardTuple ![checkName one κ]))
    (hδ : IsWoodinPrefixCutoff P R one κ δ) (hPδ : P ∈ hierarchy δ) {G : Set V}
    (hG : IsExternalForcingGeneric
      (twoStepConditions P R (woodinPrefixPosetName P R one κ δ) (forcedEmptyName P R))
      (twoStepOrder P R (woodinPrefixPosetName P R one κ δ) (woodinPrefixOrderName P R one κ δ)
        (forcedEmptyName P R)) G) :
    IsRegularCardinal ((woodinPrefixSuccessorContext hR htop hκ hδ hG).check δ) := by
  let h := woodinPrefix_iterand hR htop hκ hδ
  let A := twoStepFirstContext hR htop h hG
  let B := twoStepSecondContext hR htop h hG
  let C := woodinPrefixSuccessorContext hR htop hκ hδ hG
  let cκ : ForcingName A.P := ⟨checkName one κ, checkName_isName htop.1 κ⟩
  let cδ : ForcingName A.P := ⟨checkName one δ, checkName_isName htop.1 δ⟩
  let := hδ.2.1.1
  let : IsOrdinal (A.ofName cδ) := by change IsOrdinal (A.check δ); infer_instance
  have hBP : B.P = woodinCollapse (A.check κ) (A.check δ) := A.collapseName_value_of_ordinal cκ cδ
  have hBR : B.R = woodinCollapseOrder (A.check κ) (A.check δ) := by
    change A.ofName (A.reverseOrderName (A.collapseName cκ cδ)) = _
    rw [A.reverseOrderName_value]
    exact congrArg reverseInclusionOrder hBP
  have hBo : B.one = ∅ := A.forcedEmptyName_value
  have hk : IsRegularCardinal (A.check κ) := by
    obtain ⟨p, hp⟩ := A.generic.1.2.1
    exact (Defined.eval_iff _).mp ((A.checked_unary_truth regularCardinalFormula κ).mpr
      ⟨p, hp, hκ p (A.generic.1.1 p hp)⟩)
  have hr := B.check_regular_of_collapse hk (A.check_inaccessible_of_small hδ.2.1 hPδ)
    ((A.check_mem_iff _ _).mpr hδ.1) hBP hBR hBo
  have he := (twoStepQuotientElementaryMap hR htop h hG).map_defined regularCardinalFormula
    (fun v : Fin 1 → C.Model ↦ IsRegularCardinal (v 0))
    (fun v : Fin 1 → B.Model ↦ IsRegularCardinal (v 0)) ![C.check δ]
  apply he.mpr
  change IsRegularCardinal (twoStepQuotientEquiv hR htop h hG (C.check δ))
  exact (twoStepQuotientEquiv_check hR htop h hG δ).symm ▸ hr

end ZFVP
