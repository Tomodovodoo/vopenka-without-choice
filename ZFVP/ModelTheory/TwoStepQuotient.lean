import ZFVP.ModelTheory.TwoStepEquivalence
import ZFVP.ModelTheory.ForcingContextCongruence

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable {P R Q S t one : V} (hR : IsForcingPreorder P R)
  (htop : IsForcingTop P R one) (h : IsForcingIterand P R Q S t) {G : Set V}
  (hG : IsExternalForcingGeneric (twoStepConditions P R Q t) (twoStepOrder P R Q S t) G)

noncomputable def twoStepTotalContext : ForcingContext V where
  P := twoStepConditions P R Q t
  R := twoStepOrder P R Q S t
  one := ⟨one, t⟩ₖ
  G := G
  order := twoStep_preorder hR htop h
  top := twoStep_top hR htop h
  generic := hG

theorem twoStep_combinedContext_eq :
    TwoStepModel.combinedContext (twoStepFirstContext hR htop h hG) h
      (TwoStepModel.second_generic (twoStepFirstContext hR htop h hG) h hG rfl) =
        twoStepTotalContext hR htop h hG := by
  apply ForcingContext.eq_of_data_eq
  · rfl
  · rfl
  · rfl
  · exact TwoStepModel.original_combination (twoStepFirstContext hR htop h hG) h hG rfl

noncomputable def twoStepQuotientEquiv : (twoStepTotalContext hR htop h hG).Model ≃
    (twoStepSecondContext hR htop h hG).Model :=
  (ForcingContext.modelCongr (twoStep_combinedContext_eq hR htop h hG).symm).trans
    (TwoStepModel.combinedEquiv (twoStepFirstContext hR htop h hG) h
      (TwoStepModel.second_generic (twoStepFirstContext hR htop h hG) h hG rfl))

theorem twoStepQuotientEquiv_mem_iff (x y : (twoStepTotalContext hR htop h hG).Model) :
    twoStepQuotientEquiv hR htop h hG x ∈ twoStepQuotientEquiv hR htop h hG y ↔ x ∈ y := by
  let A := twoStepFirstContext hR htop h hG
  let hH := TwoStepModel.second_generic A h hG rfl
  let hc := (twoStep_combinedContext_eq hR htop h hG).symm
  exact (TwoStepModel.combinedEquiv_mem_iff A h hH
    (ForcingContext.modelCongr hc x) (ForcingContext.modelCongr hc y)).trans
      (ForcingContext.modelCongr_mem_iff hc x y)

theorem twoStepQuotientEquiv_check (x : V) :
    twoStepQuotientEquiv hR htop h hG ((twoStepTotalContext hR htop h hG).check x) =
      (twoStepSecondContext hR htop h hG).check ((twoStepFirstContext hR htop h hG).check x) := by
  let A := twoStepFirstContext hR htop h hG
  let hH := TwoStepModel.second_generic A h hG rfl
  let hc := (twoStep_combinedContext_eq hR htop h hG).symm
  exact (congrArg (TwoStepModel.combinedEquiv A h hH) (ForcingContext.modelCongr_check hc x)).trans
    (TwoStepModel.combinedEquiv_check A h hH x)

noncomputable def twoStepQuotientElementaryMap : ElementaryMap (twoStepTotalContext hR htop h hG).Model
    (twoStepSecondContext hR htop h hG).Model :=
  ElementaryMap.ofMembershipIso (twoStepQuotientEquiv hR htop h hG)
    (twoStepQuotientEquiv_mem_iff hR htop h hG)

end ZFVP
