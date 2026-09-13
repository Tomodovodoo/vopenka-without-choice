import ZFVP.ModelTheory.SaturatedWoodinIterand
import ZFVP.ModelTheory.WoodinPrefixRegular

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def woodinStageCardinalFormula : SetTheorySemisentence 1 :=
  regularCardinalFormula.and dependentChoiceBelowFormula

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

instance woodinStageCardinalFormula_defined :
    ℒₛₑₜ-predicate[V] (fun δ ↦ IsRegularCardinal δ ∧ ∀ η ∈ δ, InternalDependentChoiceAt η)
      via woodinStageCardinalFormula := ⟨fun v ↦ by
    change regularCardinalFormula.Evalb v ∧ dependentChoiceBelowFormula.Evalb v ↔ _
    simp⟩

theorem ForcingContext.rawEmptyName_value (A : ForcingContext V) :
    A.ofName ⟨∅, empty_forcingName A.P⟩ = ∅ := by
  apply mem_ext
  intro x
  rw [A.mem_ofName_iff]
  simp

theorem saturatedWoodinPrefix_iterand_of_cutoff {P R one κ δ : V}
    (hR : IsForcingPreorder P R) (htop : IsForcingTop P R one)
    (hκ : ∀ p ∈ P, p ∈ forcingFormula P R regularCardinalFormula (standardTuple ![checkName one κ]))
    (hδ : IsWoodinPrefixCutoff P R one κ δ) (hP : P ∈ hierarchy δ) :
    IsForcingIterand P R (saturatedWoodinPrefixPosetName P R one κ δ)
      (saturatedWoodinPrefixOrderName P R one κ δ) ∅ := by
  let := hδ.2.1.1
  exact saturatedWoodinPrefix_iterand hR htop hδ.2.1 hP (IsOrdinal.toIsTransitive.transitive _ hδ.1) hκ

variable {P R one κ δ : V} (hR : IsForcingPreorder P R) (htop : IsForcingTop P R one)
  (hκ : ∀ p ∈ P, p ∈ forcingFormula P R regularCardinalFormula (standardTuple ![checkName one κ]))
  (hδ : IsWoodinPrefixCutoff P R one κ δ) (hP : P ∈ hierarchy δ) {G : Set V}
  (hG : IsExternalForcingGeneric
    (twoStepConditions P R (saturatedWoodinPrefixPosetName P R one κ δ) ∅)
    (twoStepOrder P R (saturatedWoodinPrefixPosetName P R one κ δ)
      (saturatedWoodinPrefixOrderName P R one κ δ) ∅) G)

noncomputable def saturatedWoodinSuccessorContext : ForcingContext V :=
  twoStepTotalContext hR htop (saturatedWoodinPrefix_iterand_of_cutoff hR htop hκ hδ hP) hG

theorem saturatedWoodinSuccessor_cardinal :
    IsRegularCardinal ((saturatedWoodinSuccessorContext hR htop hκ hδ hP hG).check δ) ∧
      ∀ η ∈ (saturatedWoodinSuccessorContext hR htop hκ hδ hP hG).check δ, InternalDependentChoiceAt η := by
  let h := saturatedWoodinPrefix_iterand_of_cutoff hR htop hκ hδ hP
  let A := twoStepFirstContext hR htop h hG
  let B := twoStepSecondContext hR htop h hG
  let C := saturatedWoodinSuccessorContext hR htop hκ hδ hP hG
  let := hδ.2.1.1
  have hκδ : κ ⊆ δ := IsOrdinal.toIsTransitive.transitive _ hδ.1
  have hBP : B.P = woodinCollapse (A.check κ) (A.check δ) := A.saturatedWoodinPosetName_value hδ.2.1 hP hκδ
  have hBR : B.R = woodinCollapseOrder (A.check κ) (A.check δ) := A.saturatedWoodinOrderName_value hδ.2.1 hP hκδ
  have hBo : B.one = ∅ := A.rawEmptyName_value
  have hk : IsRegularCardinal (A.check κ) := by
    obtain ⟨p, hp⟩ := A.generic.1.2.1
    exact (Defined.eval_iff _).mp ((A.checked_unary_truth regularCardinalFormula κ).mpr
      ⟨p, hp, hκ p (A.generic.1.1 p hp)⟩)
  have hr := B.check_regular_of_collapse hk (A.check_inaccessible_of_small hδ.2.1 hP)
    ((A.check_mem_iff _ _).mpr hδ.1) hBP hBR hBo
  have hDC := B.dependentChoice_of_localRestoration (hδ.localRestoration A) hBP hBR hBo
  have he := (twoStepQuotientElementaryMap hR htop h hG).map_defined woodinStageCardinalFormula
    (fun v : Fin 1 → C.Model ↦ IsRegularCardinal (v 0) ∧ ∀ η ∈ v 0, InternalDependentChoiceAt η)
    (fun v : Fin 1 → B.Model ↦ IsRegularCardinal (v 0) ∧ ∀ η ∈ v 0, InternalDependentChoiceAt η) ![C.check δ]
  apply he.mpr
  change IsRegularCardinal (twoStepQuotientEquiv hR htop h hG (C.check δ)) ∧
    ∀ η ∈ twoStepQuotientEquiv hR htop h hG (C.check δ), InternalDependentChoiceAt η
  exact (twoStepQuotientEquiv_check hR htop h hG δ).symm ▸ ⟨hr, hDC⟩

end ZFVP
