import ZFVP.ModelTheory.TwoStepSecondGeneric

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace TwoStepModel
variable (A : ForcingContext V) {Q S t : V} (h : IsForcingIterand A.P A.R Q S t)

theorem top : IsForcingTop (A.ofName ⟨Q, h.posetName⟩)
    (A.ofName ⟨S, h.orderName⟩) (A.ofName ⟨t, h.topName⟩) := by
  obtain ⟨p, hp⟩ := A.generic.1.2.1
  exact (Defined.eval_iff _).mp ((A.formula_truth forcingTopFormula
    ![⟨Q, h.posetName⟩, ⟨S, h.orderName⟩, ⟨t, h.topName⟩]).mpr
      ⟨p, hp, h.top p (A.generic.1.1 p hp)⟩)

noncomputable def secondContext {G : Set V}
    (hG : IsExternalForcingGeneric (twoStepConditions A.P A.R Q t) (twoStepOrder A.P A.R Q S t) G)
    (hA : A.G = forcingProjectionGeneric A.P A.R (twoStepProjection A.P A.R Q t) G) :
    ForcingContext A.Model where
  P := A.ofName ⟨Q, h.posetName⟩
  R := A.ofName ⟨S, h.orderName⟩
  one := A.ofName ⟨t, h.topName⟩
  G := twoStepSecondFilter A ⟨Q, h.posetName⟩ ⟨S, h.orderName⟩ G
  order := preorder A h
  top := top A h
  generic := second_generic A h hG hA

end TwoStepModel

variable {P R Q S t one : V} (hR : IsForcingPreorder P R)
  (htop : IsForcingTop P R one) (h : IsForcingIterand P R Q S t) {G : Set V}
  (hG : IsExternalForcingGeneric (twoStepConditions P R Q t) (twoStepOrder P R Q S t) G)

def twoStepFirstContext : ForcingContext V where
  P := P
  R := R
  one := one
  G := forcingProjectionGeneric P R (twoStepProjection P R Q t) G
  order := hR
  top := htop
  generic := twoStep_projected_generic hR htop h hG

noncomputable def twoStepSecondContext : ForcingContext (twoStepFirstContext hR htop h hG).Model :=
  TwoStepModel.secondContext (twoStepFirstContext hR htop h hG) h hG rfl

end ZFVP
