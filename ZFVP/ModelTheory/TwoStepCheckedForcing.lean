import ZFVP.ModelTheory.ForcingCheckedTruth
import ZFVP.ModelTheory.TwoStepCheckedSemantics

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

def allCheckedForcingFormula (φ : SetTheorySemisentence 1) : SetTheorySemisentence 4 :=
  f“Q S t a. ∀ p ∈ Q, !(checkedUnaryForcingFormula φ) Q S t p a”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem eval_allCheckedForcingFormula (φ : SetTheorySemisentence 1) (v : Fin 4 → V) :
    (allCheckedForcingFormula φ).Evalb v ↔
      ∀ p ∈ v 0, p ∈ forcingFormula (v 0) (v 1) φ (standardTuple ![checkName (v 2) (v 3)]) := by
  simp [allCheckedForcingFormula]

theorem twoStep_checked_forcing_countable [Countable V] {P R Q S t one a : V}
    (hR : IsForcingPreorder P R) (htop : IsForcingTop P R one)
    (h : IsForcingIterand P R Q S t) (φ : SetTheorySemisentence 1) :
    (∀ p ∈ P, p ∈ forcingFormula P R (allCheckedForcingFormula φ)
      (standardTuple ![Q, S, t, checkName one a])) ↔
    (∀ p ∈ twoStepConditions P R Q t,
      p ∈ forcingFormula (twoStepConditions P R Q t) (twoStepOrder P R Q S t) φ
        (standardTuple ![checkName ⟨one, t⟩ₖ a])) := by
  let v : Fin 4 → ForcingName P :=
    ![⟨Q, h.posetName⟩, ⟨S, h.orderName⟩, ⟨t, h.topName⟩,
      ⟨checkName one a, checkName_isName htop.1 a⟩]
  have hfirst := all_forces_iff_all_generics hR htop (allCheckedForcingFormula φ) v
  have htotal := all_forces_checked_iff_all_generics
    (twoStep_preorder hR htop h) (twoStep_top hR htop h) (a := a) φ
  have hsplit := twoStep_all_checked_iff_successive hR htop h φ (fun _ ↦ a)
  refine hfirst.trans ?_
  refine Iff.trans ?_ (hsplit.symm.trans htotal.symm)
  constructor
  · intro hall G hG
    dsimp only
    intro H hH
    let A : ForcingContext V := ⟨P, R, one, G, hR, htop, hG⟩
    have hf := (eval_allCheckedForcingFormula φ (fun i ↦ A.ofName (v i))).mp (hall G hG)
    exact (all_forces_checked_iff_all_generics (TwoStepModel.preorder A h)
      (TwoStepModel.top A h) (a := A.check a) φ).mp hf H hH
  · intro hall G hG
    let A : ForcingContext V := ⟨P, R, one, G, hR, htop, hG⟩
    apply (eval_allCheckedForcingFormula φ (fun i ↦ A.ofName (v i))).mpr
    exact (all_forces_checked_iff_all_generics (TwoStepModel.preorder A h)
      (TwoStepModel.top A h) (a := A.check a) φ).mpr (hall G hG)

end ZFVP
