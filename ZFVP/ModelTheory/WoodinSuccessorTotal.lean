import ZFVP.ModelTheory.WoodinSuccessorRestoration
import ZFVP.ModelTheory.TwoStepIntermediate

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace WoodinSuccessorModel
variable (A : ForcingContext V) (κ : ForcingName A.P)
  (hκ : ∀ p ∈ A.P, p ∈ forcingFormula A.P A.R regularCardinalFormula (standardTuple ![κ.val]))
  {H : Set A.Model}
  (hH : IsExternalForcingGeneric (A.ofName (A.successorPosetName κ))
    (A.ofName (A.reverseOrderName (A.successorPosetName κ))) H)

noncomputable def combinedCutoff :
    (TwoStepModel.combinedContext A (woodinSuccessor_iterand A.order A.top κ hκ) hH).Model :=
  (TwoStepModel.combinedEquiv A (woodinSuccessor_iterand A.order A.top κ hκ) hH).symm
    ((context A κ hκ hH).check (woodinRestorationCutoff (A.ofName κ)))

theorem combined_restores {δ : A.Model} (hδ : IsWoodinRestorationCutoff (A.ofName κ) δ) :
    ∀ η ∈ combinedCutoff A κ hκ hH, InternalDependentChoiceAt η := by
  let h := woodinSuccessor_iterand A.order A.top κ hκ
  let C := TwoStepModel.combinedContext A h hH
  let B := context A κ hκ hH
  let e := TwoStepModel.combinedEquiv A h hH
  have ht := (TwoStepModel.combinedElementaryMap A h hH).map_defined dependentChoiceBelowFormula
    (fun v : Fin 1 → C.Model ↦ ∀ η ∈ v 0, InternalDependentChoiceAt η)
    (fun v : Fin 1 → B.Model ↦ ∀ η ∈ v 0, InternalDependentChoiceAt η) ![combinedCutoff A κ hκ hH]
  apply ht.mpr
  change ∀ η ∈ e (e.symm (B.check (woodinRestorationCutoff (A.ofName κ)))), InternalDependentChoiceAt η
  exact (e.apply_symm_apply (B.check (woodinRestorationCutoff (A.ofName κ)))).symm ▸
    restores A κ hκ hH hδ

end WoodinSuccessorModel

variable {P R one : V} (hR : IsForcingPreorder P R) (htop : IsForcingTop P R one)
  (κ : ForcingName P)
  (hκ : ∀ p ∈ P, p ∈ forcingFormula P R regularCardinalFormula (standardTuple ![κ.val]))
  {G : Set V}
  (hG : IsExternalForcingGeneric
    (twoStepConditions P R (woodinSuccessorPosetName P R κ.val) (forcedEmptyName P R))
    (twoStepOrder P R (woodinSuccessorPosetName P R κ.val)
      (reverseInclusionOrderName P R (woodinSuccessorPosetName P R κ.val)) (forcedEmptyName P R)) G)

noncomputable def woodinSuccessorTotalCutoff :
    (twoStepTotalContext hR htop (woodinSuccessor_iterand hR htop κ hκ) hG).Model :=
  let h := woodinSuccessor_iterand hR htop κ hκ
  let A := twoStepFirstContext hR htop h hG
  twoStepIntermediateEmbedding hR htop h hG (woodinRestorationCutoff (A.ofName κ))

theorem woodinSuccessorTotal_restores
    {δ : (twoStepFirstContext hR htop (woodinSuccessor_iterand hR htop κ hκ) hG).Model}
    (hδ : IsWoodinRestorationCutoff
      ((twoStepFirstContext hR htop (woodinSuccessor_iterand hR htop κ hκ) hG).ofName κ) δ) :
    ∀ η ∈ woodinSuccessorTotalCutoff hR htop κ hκ hG, InternalDependentChoiceAt η := by
  let h := woodinSuccessor_iterand hR htop κ hκ
  let A := twoStepFirstContext hR htop h hG
  let B := twoStepSecondContext hR htop h hG
  let C := twoStepTotalContext hR htop h hG
  let cutoff := woodinRestorationCutoff (A.ofName κ)
  have ht := (twoStepQuotientElementaryMap hR htop h hG).map_defined dependentChoiceBelowFormula
    (fun v : Fin 1 → C.Model ↦ ∀ η ∈ v 0, InternalDependentChoiceAt η)
    (fun v : Fin 1 → B.Model ↦ ∀ η ∈ v 0, InternalDependentChoiceAt η)
    ![woodinSuccessorTotalCutoff hR htop κ hκ hG]
  apply ht.mpr
  change ∀ η ∈ twoStepQuotientEquiv hR htop h hG (twoStepIntermediateEmbedding hR htop h hG cutoff),
    InternalDependentChoiceAt η
  rw [twoStepQuotientEquiv_intermediate]
  exact WoodinSuccessorModel.restores A κ hκ (TwoStepModel.second_generic A h hG rfl) hδ

end ZFVP
