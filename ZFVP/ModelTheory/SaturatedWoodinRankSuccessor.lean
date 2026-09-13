import ZFVP.ModelTheory.WoodinCollapseRankInvariant
import ZFVP.ModelTheory.SaturatedWoodinSuccessor

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

variable {P R one κ δ θ : V} (hR : IsForcingPreorder P R) (htop : IsForcingTop P R one)
  (hκ : ∀ p ∈ P, p ∈ forcingFormula P R regularCardinalFormula (standardTuple ![checkName one κ]))
  (hδ : IsWoodinPrefixCutoff P R one κ δ) (hP : P ∈ hierarchy δ) {G : Set V}
  (hG : IsExternalForcingGeneric
    (twoStepConditions P R (saturatedWoodinPrefixPosetName P R one κ δ) ∅)
    (twoStepOrder P R (saturatedWoodinPrefixPosetName P R one κ δ)
      (saturatedWoodinPrefixOrderName P R one κ δ) ∅) G)

/-- The rank enumeration invariant passes through the saturated successor presentation. -/
theorem saturatedWoodinSuccessor_rankEnumerations (hθ : θ ∈ δ)
    (hDC : ∀ p ∈ P, p ∈ forcingFormula P R dependentChoiceBelowFormula
      (standardTuple ![checkName one κ]))
    (henum : ∀ p ∈ P, p ∈ forcingFormula P R shortRankEnumerationsFormula
      (standardTuple ![checkName one θ, checkName one κ])) :
    HasShortRankEnumerations
      ((saturatedWoodinSuccessorContext hR htop hκ hδ hP hG).check (succ θ))
      ((saturatedWoodinSuccessorContext hR htop hκ hδ hP hG).check δ) := by
  let h := saturatedWoodinPrefix_iterand_of_cutoff hR htop hκ hδ hP
  let A := twoStepFirstContext hR htop h hG
  let B := twoStepSecondContext hR htop h hG
  let C := saturatedWoodinSuccessorContext hR htop hκ hδ hP hG
  let := hδ.2.1.1
  have hκδ : κ ⊆ δ := IsOrdinal.toIsTransitive.transitive _ hδ.1
  have hBP : B.P = woodinCollapse (A.check κ) (A.check δ) := A.saturatedWoodinPosetName_value hδ.2.1 hP hκδ
  have hBR : B.R = woodinCollapseOrder (A.check κ) (A.check δ) := A.saturatedWoodinOrderName_value hδ.2.1 hP hκδ
  have hBo : B.one = ∅ := A.rawEmptyName_value
  obtain ⟨p, hp⟩ := A.generic.1.2.1
  have hpP := A.generic.1.1 p hp
  have hk : IsRegularCardinal (A.check κ) :=
    (Defined.eval_iff _).mp ((A.checked_unary_truth regularCardinalFormula κ).mpr ⟨p, hp, hκ p hpP⟩)
  have hd : ∀ γ ∈ A.check κ, InternalDependentChoiceAt γ :=
    (Defined.eval_iff _).mp ((A.checked_unary_truth dependentChoiceBelowFormula κ).mpr ⟨p, hp, hDC p hpP⟩)
  have hrank : HasShortRankEnumerations (A.check θ) (A.check κ) :=
    (Defined.eval_iff _).mp ((A.formula_truth shortRankEnumerationsFormula
      ![⟨checkName one θ, checkName_isName htop.1 θ⟩,
        ⟨checkName one κ, checkName_isName htop.1 κ⟩]).mpr ⟨p, hp, henum p hpP⟩)
  have hb := B.rankEnumerations_of_collapse hk (A.check_inaccessible_of_small hδ.2.1 hP).regular
    ((A.check_mem_iff _ _).mpr hδ.1) ((A.check_mem_iff _ _).mpr hθ) hd hrank hBP hBR hBo
  apply ((twoStepQuotientElementaryMap hR htop h hG).shortRankEnumerations_iff
    (C.check (succ θ)) (C.check δ)).mpr
  change HasShortRankEnumerations
    (twoStepQuotientEquiv hR htop h hG ((twoStepTotalContext hR htop h hG).check (succ θ)))
    (twoStepQuotientEquiv hR htop h hG ((twoStepTotalContext hR htop h hG).check δ))
  rw [twoStepQuotientEquiv_check hR htop h hG (succ θ), twoStepQuotientEquiv_check hR htop h hG δ]
  change HasShortRankEnumerations (B.check (A.check (succ θ))) (B.check (A.check δ))
  rw [show A.check (succ θ) = succ (A.check θ) from A.checkEmbedding.map_succ θ]
  exact hb

include hR htop hκ hδ hP in
theorem saturatedWoodinSuccessor_forces_rankEnumerations [Countable V] (hθ : θ ∈ δ)
    (hDC : ∀ p ∈ P, p ∈ forcingFormula P R dependentChoiceBelowFormula
      (standardTuple ![checkName one κ]))
    (henum : ∀ p ∈ P, p ∈ forcingFormula P R shortRankEnumerationsFormula
      (standardTuple ![checkName one θ, checkName one κ])) :
    ∀ p ∈ twoStepConditions P R (saturatedWoodinPrefixPosetName P R one κ δ) ∅,
      p ∈ forcingFormula (twoStepConditions P R (saturatedWoodinPrefixPosetName P R one κ δ) ∅)
        (twoStepOrder P R (saturatedWoodinPrefixPosetName P R one κ δ)
          (saturatedWoodinPrefixOrderName P R one κ δ) ∅) shortRankEnumerationsFormula
        (standardTuple ![checkName ⟨one, ∅⟩ₖ (succ θ), checkName ⟨one, ∅⟩ₖ δ]) := by
  let h := saturatedWoodinPrefix_iterand_of_cutoff hR htop hκ hδ hP
  apply (all_forces_iff_all_generics (twoStep_preorder hR htop h) (twoStep_top hR htop h)
    shortRankEnumerationsFormula
    ![⟨checkName ⟨one, ∅⟩ₖ (succ θ), checkName_isName (twoStep_top hR htop h).1 (succ θ)⟩,
      ⟨checkName ⟨one, ∅⟩ₖ δ, checkName_isName (twoStep_top hR htop h).1 δ⟩]).mpr
  intro G hG
  exact (Defined.eval_iff _).mpr (saturatedWoodinSuccessor_rankEnumerations hR htop hκ hδ hP hG hθ hDC henum)

end ZFVP
