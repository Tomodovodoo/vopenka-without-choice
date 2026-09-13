import ZFVP.ModelTheory.WoodinCollapseIterand
import ZFVP.ModelTheory.WoodinSuccessorRestoration

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def woodinPrefixPosetName (P R one κ δ : V) : V :=
  woodinCollapseName P R (checkName one κ) (checkName one δ)

noncomputable def woodinPrefixOrderName (P R one κ δ : V) : V :=
  reverseInclusionOrderName P R (woodinPrefixPosetName P R one κ δ)

theorem woodinPrefix_iterand {P R one κ δ : V} (hR : IsForcingPreorder P R)
    (htop : IsForcingTop P R one)
    (hκ : ∀ p ∈ P, p ∈ forcingFormula P R regularCardinalFormula (standardTuple ![checkName one κ]))
    (hδ : IsWoodinPrefixCutoff P R one κ δ) :
    IsForcingIterand P R (woodinPrefixPosetName P R one κ δ) (woodinPrefixOrderName P R one κ δ)
      (forcedEmptyName P R) :=
  woodinCollapse_iterand hR htop ⟨checkName one κ, checkName_isName htop.1 κ⟩
    ⟨checkName one δ, checkName_isName htop.1 δ⟩ hκ hδ.2.2

theorem ForcingContext.dependentChoice_of_localRestoration (A : ForcingContext V) {κ δ : V}
    (hδ : IsWoodinLocalRestoration κ δ) (hP : A.P = woodinCollapse κ δ)
    (hR : A.R = woodinCollapseOrder κ δ) (ho : A.one = ∅) :
    ∀ η ∈ A.check δ, InternalDependentChoiceAt η := by
  let c : ForcingName A.P := ⟨checkName A.one δ, checkName_isName A.top.1 δ⟩
  obtain ⟨p, hp⟩ := A.generic.1.2.1
  have hpP : p ∈ woodinCollapse κ δ := hP ▸ A.generic.1.1 p hp
  have hf : p ∈ forcingFormula A.P A.R dependentChoiceBelowFormula (standardTuple ![c.val]) := by
    change p ∈ forcingFormula A.P A.R dependentChoiceBelowFormula (standardTuple ![checkName A.one δ])
    rw [hP, hR, ho]
    exact hδ.2 p hpP
  exact (Defined.eval_iff _).mp ((A.formula_truth dependentChoiceBelowFormula ![c]).mpr ⟨p, hp, hf⟩)

variable {P R one κ δ : V} (hR : IsForcingPreorder P R) (htop : IsForcingTop P R one)
  (hκ : ∀ p ∈ P, p ∈ forcingFormula P R regularCardinalFormula (standardTuple ![checkName one κ]))
  (hδ : IsWoodinPrefixCutoff P R one κ δ) {G : Set V}
  (hG : IsExternalForcingGeneric
    (twoStepConditions P R (woodinPrefixPosetName P R one κ δ) (forcedEmptyName P R))
    (twoStepOrder P R (woodinPrefixPosetName P R one κ δ) (woodinPrefixOrderName P R one κ δ)
      (forcedEmptyName P R)) G)

noncomputable def woodinPrefixSuccessorContext : ForcingContext V :=
  twoStepTotalContext hR htop (woodinPrefix_iterand hR htop hκ hδ) hG

theorem woodinPrefixSuccessor_restores :
    ∀ η ∈ (woodinPrefixSuccessorContext hR htop hκ hδ hG).check δ, InternalDependentChoiceAt η := by
  let h := woodinPrefix_iterand hR htop hκ hδ
  let A := twoStepFirstContext hR htop h hG
  let B := twoStepSecondContext hR htop h hG
  let C := woodinPrefixSuccessorContext hR htop hκ hδ hG
  let cκ : ForcingName A.P := ⟨checkName one κ, checkName_isName htop.1 κ⟩
  let cδ : ForcingName A.P := ⟨checkName one δ, checkName_isName htop.1 δ⟩
  let := hδ.2.1.1
  let : IsOrdinal (A.ofName cδ) := by
    change IsOrdinal (A.check δ)
    infer_instance
  have hP : B.P = woodinCollapse (A.check κ) (A.check δ) :=
    A.collapseName_value_of_ordinal cκ cδ
  have hR' : B.R = woodinCollapseOrder (A.check κ) (A.check δ) := by
    change A.ofName (A.reverseOrderName (A.collapseName cκ cδ)) = _
    rw [A.reverseOrderName_value]
    exact congrArg reverseInclusionOrder hP
  have ho : B.one = ∅ := A.forcedEmptyName_value
  have hr := B.dependentChoice_of_localRestoration (hδ.localRestoration A) hP hR' ho
  have he := (twoStepQuotientElementaryMap hR htop h hG).map_defined dependentChoiceBelowFormula
    (fun v : Fin 1 → C.Model ↦ ∀ η ∈ v 0, InternalDependentChoiceAt η)
    (fun v : Fin 1 → B.Model ↦ ∀ η ∈ v 0, InternalDependentChoiceAt η) ![C.check δ]
  apply he.mpr
  change ∀ η ∈ twoStepQuotientEquiv hR htop h hG (C.check δ), InternalDependentChoiceAt η
  exact (twoStepQuotientEquiv_check hR htop h hG δ).symm ▸ hr

end ZFVP
