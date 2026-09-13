import ZFVP.ModelTheory.DeltaOneForcingCodeNext
import ZFVP.ModelTheory.WoodinIterationInitial

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

def sigmaOneForcingInitialCodeFormula : SetTheorySemisentence 4 :=
  “z P R o. ∃ e, !boundedEmptyFormula e ∧
    ∃ Pt, !sigmaOneFamilyNextFormula Pt e e P ∧ ∃ Rt, !sigmaOneFamilyNextFormula Rt e e R ∧
    ∃ I, !boundedIdentityFormula I P ∧ ∃ J, !sigmaOneIdentityLiftFormula J P ∧
    ∃ π, !sigmaOneMatrixNextFormula π e e e I ∧ ∃ L, !sigmaOneMatrixNextFormula L e e e J ∧
    ∃ t, !sigmaOneFamilyNextFormula t e e o ∧ !boundedForcingCodeFormula z Pt Rt π π L t”

theorem sigmaOneForcingInitialCodeFormula_sigmaOne : IsSigmaFormula 1 sigmaOneForcingInitialCodeFormula :=
  .exs (.and (.bounded (boundedEmptyFormula_bounded.subst _))
    (.exs (.and (sigmaOneFamilyNextFormula_sigmaOne.subst _)
      (.exs (.and (sigmaOneFamilyNextFormula_sigmaOne.subst _)
        (.exs (.and (.bounded (boundedIdentityFormula_bounded.subst _))
          (.exs (.and (sigmaOneIdentityLiftFormula_sigmaOne.subst _)
            (.exs (.and (sigmaOneMatrixNextFormula_sigmaOne.subst _)
              (.exs (.and (sigmaOneMatrixNextFormula_sigmaOne.subst _)
                (.exs (.and (sigmaOneFamilyNextFormula_sigmaOne.subst _)
                  (.bounded (boundedForcingCodeFormula_bounded.subst _)))))))))))))))))

def piOneForcingInitialCodeFormula : SetTheorySemisentence 4 :=
  “z P R o. ∀ w, !sigmaOneForcingInitialCodeFormula w P R o → z = w”

theorem piOneForcingInitialCodeFormula_piOne : IsPiFormula 1 piOneForcingInitialCodeFormula :=
  .all (.or (sigmaOneForcingInitialCodeFormula_sigmaOne.subst _).neg (.bounded (.rel _ _)))

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

instance sigmaOneForcingInitialCodeFormula_defined :
    ℒₛₑₜ-function₃[V] forcingInitialCode via sigmaOneForcingInitialCodeFormula :=
  ⟨fun v ↦ by simp [sigmaOneForcingInitialCodeFormula, forcingInitialCode]⟩

instance piOneForcingInitialCodeFormula_defined :
    ℒₛₑₜ-function₃[V] forcingInitialCode via piOneForcingInitialCodeFormula :=
  ⟨fun v ↦ by simp [piOneForcingInitialCodeFormula]⟩

end ZFVP
