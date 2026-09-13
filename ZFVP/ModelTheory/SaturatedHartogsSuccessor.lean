import ZFVP.ModelTheory.SaturatedHartogsCollapse
import ZFVP.ModelTheory.SaturatedWoodinSuccessor
import ZFVP.SetTheory.WoodinNamedPrefixCutoff
import ZFVP.ModelTheory.ForcingCheckedBounded

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem saturatedHartogsCollapse_iterand {P R one γ δ : V}
    (hR : IsForcingPreorder P R) (htop : IsForcingTop P R one)
    (hδ : IsChoicelessInaccessible δ)
    (hκ : ∀ p ∈ P, p ∈ forcingFormula P R regularCardinalFormula
      (standardTuple ![hartogsNumberName P R (checkName one γ)])) :
    IsForcingIterand P R
      (saturatedWoodinCollapseName P R δ (hartogsNumberName P R (checkName one γ)) (checkName one δ))
      (reverseInclusionOrderName P R
        (saturatedWoodinCollapseName P R δ (hartogsNumberName P R (checkName one γ)) (checkName one δ))) ∅ := by
  let := hδ.1
  exact saturatedWoodinCollapse_empty_iterand hR htop
    ⟨hartogsNumberName P R (checkName one γ), hartogsNumberName_isName _ _ _⟩
    ⟨checkName one δ, checkName_isName htop.1 _⟩
    ((mem_forcingNameHierarchy P δ ∅).mpr ⟨∅, hδ.regular.2.1 ∅ (by simp), by simp⟩)
    hκ (fun _ hp ↦ forces_checked_ordinal hR htop inferInstance hp)

variable {P R one γ δ : V} (hR : IsForcingPreorder P R) (htop : IsForcingTop P R one)
  (hκ : ∀ p ∈ P, p ∈ forcingFormula P R regularCardinalFormula
    (standardTuple ![hartogsNumberName P R (checkName one γ)]))
  (hδ : IsWoodinNamedPrefixCutoff P R one γ (hartogsNumberName P R (checkName one γ)) δ)
  (hP : P ∈ hierarchy δ) {G : Set V}
  (hG : IsExternalForcingGeneric
    (twoStepConditions P R
      (saturatedWoodinCollapseName P R δ (hartogsNumberName P R (checkName one γ)) (checkName one δ)) ∅)
    (twoStepOrder P R
      (saturatedWoodinCollapseName P R δ (hartogsNumberName P R (checkName one γ)) (checkName one δ))
      (reverseInclusionOrderName P R
        (saturatedWoodinCollapseName P R δ (hartogsNumberName P R (checkName one γ)) (checkName one δ))) ∅) G)

noncomputable def saturatedHartogsSuccessorContext : ForcingContext V :=
  twoStepTotalContext hR htop (saturatedHartogsCollapse_iterand hR htop hδ.2.1 hκ) hG

include hP in
theorem saturatedHartogsSuccessor_cardinal :
    IsRegularCardinal ((saturatedHartogsSuccessorContext hR htop hκ hδ hG).check δ) ∧
      ∀ η ∈ (saturatedHartogsSuccessorContext hR htop hκ hδ hG).check δ, InternalDependentChoiceAt η := by
  let h := saturatedHartogsCollapse_iterand hR htop hδ.2.1 hκ
  let A := twoStepFirstContext hR htop h hG
  let B := twoStepSecondContext hR htop h hG
  let C := saturatedHartogsSuccessorContext hR htop hκ hδ hG
  let := hδ.2.1.1
  let τ : ForcingName A.P := ⟨checkName A.one γ, checkName_isName A.top.1 _⟩
  let κ := A.hartogsName τ
  have hv : A.ofName κ = hartogsNumber (A.check γ) := A.hartogsName_value τ
  have hBP : B.P = woodinCollapse (hartogsNumber (A.check γ)) (A.check δ) :=
    A.saturatedHartogsCollapseName_value hδ.2.1 hP hδ.1
  have hBR : B.R = woodinCollapseOrder (hartogsNumber (A.check γ)) (A.check δ) :=
    A.saturatedHartogsCollapseOrderName_value hδ.2.1 hP hδ.1
  have hBo : B.one = ∅ := A.rawEmptyName_value
  have hk : IsRegularCardinal (hartogsNumber (A.check γ)) := by
    rw [← hv]
    obtain ⟨p, hp⟩ := A.generic.1.2.1
    exact (Defined.eval_iff _).mp ((A.formula_truth regularCardinalFormula ![κ]).mpr
      ⟨p, hp, hκ p (A.generic.1.1 p hp)⟩)
  have hr := B.check_regular_of_collapse hk (A.check_inaccessible_of_small hδ.2.1 hP)
    (A.hartogs_checked_mem hδ.2.1 hP hδ.1) hBP hBR hBo
  have hl : IsWoodinLocalRestoration (hartogsNumber (A.check γ)) (A.check δ) :=
    hv ▸ hδ.localRestoration A κ
  have hDC := B.dependentChoice_of_localRestoration hl hBP hBR hBo
  have he := (twoStepQuotientElementaryMap hR htop h hG).map_defined woodinStageCardinalFormula
    (fun v : Fin 1 → C.Model ↦ IsRegularCardinal (v 0) ∧ ∀ η ∈ v 0, InternalDependentChoiceAt η)
    (fun v : Fin 1 → B.Model ↦ IsRegularCardinal (v 0) ∧ ∀ η ∈ v 0, InternalDependentChoiceAt η) ![C.check δ]
  apply he.mpr
  change IsRegularCardinal (twoStepQuotientEquiv hR htop h hG (C.check δ)) ∧
    ∀ η ∈ twoStepQuotientEquiv hR htop h hG (C.check δ), InternalDependentChoiceAt η
  exact (twoStepQuotientEquiv_check hR htop h hG δ).symm ▸ ⟨hr, hDC⟩

end ZFVP

