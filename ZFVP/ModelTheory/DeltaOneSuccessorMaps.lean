import ZFVP.ModelTheory.ForcingSuccessorUniform
import ZFVP.SetTheory.DeltaOnePairProjections
import ZFVP.SetTheory.LevyGraphAssembly
import ZFVP.SetTheory.BoundedValue
import ZFVP.SetTheory.BoundedProduct
import Mathlib.Tactic.FinCases

set_option maxHeartbeats 800000

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

def successorProjectionValueCertificate : SetTheorySemisentence 5 :=
  “y a π k i. ∃ j, !boundedKpairFormula j i k ∧ ∃ f, !boundedValueFormula f π j ∧
    ∃ p, !sigmaOnePairFirstFormula p a ∧ !boundedValueFormula y f p”

def successorSectionValueCertificate : SetTheorySemisentence 6 :=
  “y p E k t i. ∃ j, !boundedKpairFormula j i k ∧ ∃ f, !boundedValueFormula f E j ∧
    ∃ q, !boundedValueFormula q f p ∧ !boundedKpairFormula y q t”

def successorLiftValueCertificate : SetTheorySemisentence 3 :=
  “y z L. ∃ a, !sigmaOnePairFirstFormula a z ∧ ∃ b, !sigmaOnePairSecondFormula b z ∧
    ∃ p, !sigmaOnePairFirstFormula p a ∧ ∃ τ, !sigmaOnePairSecondFormula τ a ∧
    ∃ j, !boundedKpairFormula j p b ∧ ∃ q, !boundedValueFormula q L j ∧ !boundedKpairFormula y q τ”

theorem successorProjectionValueCertificate_sigmaOne : IsSigmaFormula 1 successorProjectionValueCertificate :=
  .exs (.and (.bounded (boundedKpairFormula_bounded.subst _))
    (.exs (.and (.bounded (boundedValueFormula_bounded.subst _))
      (.exs (.and (sigmaOnePairFirstFormula_sigmaOne.subst _) (.bounded (boundedValueFormula_bounded.subst _)))))))

theorem successorSectionValueCertificate_sigmaOne : IsSigmaFormula 1 successorSectionValueCertificate :=
  .exs (.and (.bounded (boundedKpairFormula_bounded.subst _))
    (.exs (.and (.bounded (boundedValueFormula_bounded.subst _))
      (.exs (.bounded (.and (boundedValueFormula_bounded.subst _) (boundedKpairFormula_bounded.subst _)))))))

theorem successorLiftValueCertificate_sigmaOne : IsSigmaFormula 1 successorLiftValueCertificate :=
  .exs (.and (sigmaOnePairFirstFormula_sigmaOne.subst _)
    (.exs (.and (sigmaOnePairSecondFormula_sigmaOne.subst _)
      (.exs (.and (sigmaOnePairFirstFormula_sigmaOne.subst _)
        (.exs (.and (sigmaOnePairSecondFormula_sigmaOne.subst _)
          (.exs (.and (.bounded (boundedKpairFormula_bounded.subst _))
            (.exs (.bounded (.and (boundedValueFormula_bounded.subst _) (boundedKpairFormula_bounded.subst _)))))))))))))

def sigmaOneSuccessorProjectionFormula : SetTheorySemisentence 5 :=
  graphAssemblyFormula successorProjectionValueCertificate

def sigmaOneSuccessorSectionFormula : SetTheorySemisentence 6 :=
  “G P E k t i. ∃ A, !boundedValueFormula A P i ∧
    !(graphAssemblyFormula successorSectionValueCertificate) G A E k t i”

def sigmaOneSuccessorLiftFormula : SetTheorySemisentence 4 :=
  “G C A L. ∃ D, !boundedProductFormula D C A ∧
    !(graphAssemblyFormula successorLiftValueCertificate) G D L”

theorem sigmaOneSuccessorProjectionFormula_sigmaOne : IsSigmaFormula 1 sigmaOneSuccessorProjectionFormula :=
  graphAssemblyFormula_levy successorProjectionValueCertificate_sigmaOne

theorem sigmaOneSuccessorSectionFormula_sigmaOne : IsSigmaFormula 1 sigmaOneSuccessorSectionFormula :=
  .exs (.and (.bounded (boundedValueFormula_bounded.subst _))
    ((graphAssemblyFormula_levy successorSectionValueCertificate_sigmaOne).subst _))

theorem sigmaOneSuccessorLiftFormula_sigmaOne : IsSigmaFormula 1 sigmaOneSuccessorLiftFormula :=
  .exs (.and (.bounded (boundedProductFormula_bounded.subst _))
    ((graphAssemblyFormula_levy successorLiftValueCertificate_sigmaOne).subst _))

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem eval_sigmaOneSuccessorProjectionFormula (G C π k i : V) :
    sigmaOneSuccessorProjectionFormula.Evalb ![G, C, π, k, i] ↔ G = successorStageProjection C π k i := by
  apply eval_graphAssemblyFormula successorProjectionValueCertificate G C ![π, k, i]
    (fun a ↦ (π ‘ ⟨i, k⟩ₖ) ‘ (kpair.π₁ a)) (by definability)
  intro a _ y
  simp [successorProjectionValueCertificate]

theorem eval_successorSectionGraphCertificate (G A E k t i : V) :
    (graphAssemblyFormula successorSectionValueCertificate).Evalb ![G, A, E, k, t, i] ↔
      G = definableGraph A (fun p ↦ ⟨(E ‘ ⟨i, k⟩ₖ) ‘ p, t⟩ₖ) (by definability) := by
  apply eval_graphAssemblyFormula successorSectionValueCertificate G A ![E, k, t, i]
    (fun p ↦ ⟨(E ‘ ⟨i, k⟩ₖ) ‘ p, t⟩ₖ) (by definability)
  intro p _ y
  simp [successorSectionValueCertificate]

theorem eval_sigmaOneSuccessorSectionFormula (G P E k t i : V) :
    sigmaOneSuccessorSectionFormula.Evalb ![G, P, E, k, t, i] ↔ G = successorStageSection P E k t i := by
  have he := eval_successorSectionGraphCertificate (V := V)
  simp only [Semiformula.Evalb] at he
  simp [sigmaOneSuccessorSectionFormula, Semiformula.eval_substs, Matrix.comp_vecCons',
    Matrix.constant_eq_singleton, Function.comp_def, he, successorStageSection]

theorem eval_successorLiftGraphCertificate (G D L : V) :
    (graphAssemblyFormula successorLiftValueCertificate).Evalb ![G, D, L] ↔
      G = definableGraph D (fun z ↦ successorForcingLiftValue L (kpair.π₁ z) (kpair.π₂ z)) (by definability) := by
  apply eval_graphAssemblyFormula successorLiftValueCertificate G D ![L]
    (fun z ↦ successorForcingLiftValue L (kpair.π₁ z) (kpair.π₂ z)) (by definability)
  intro z _ y
  simp [successorLiftValueCertificate, successorForcingLiftValue, twoStepStronger]

theorem eval_sigmaOneSuccessorLiftFormula (G C A L : V) :
    sigmaOneSuccessorLiftFormula.Evalb ![G, C, A, L] ↔ G = successorForcingLift C A L := by
  have he := eval_successorLiftGraphCertificate (V := V)
  simp only [Semiformula.Evalb] at he
  simp [sigmaOneSuccessorLiftFormula, Semiformula.eval_substs, Matrix.comp_vecCons',
    Matrix.constant_eq_singleton, Function.comp_def, he, successorForcingLift]

instance sigmaOneSuccessorProjectionFormula_defined :
    ℒₛₑₜ-function₄[V] successorStageProjection via sigmaOneSuccessorProjectionFormula :=
  ⟨fun v ↦ by
    have hv : v = ![v 0, v 1, v 2, v 3, v 4] := by funext i; fin_cases i <;> rfl
    change sigmaOneSuccessorProjectionFormula.Evalb v ↔ _
    rw [hv]
    exact eval_sigmaOneSuccessorProjectionFormula _ _ _ _ _⟩

instance sigmaOneSuccessorSectionFormula_defined :
    ℒₛₑₜ-function₅[V] successorStageSection via sigmaOneSuccessorSectionFormula :=
  ⟨fun v ↦ by
    have hv : v = ![v 0, v 1, v 2, v 3, v 4, v 5] := by funext i; fin_cases i <;> rfl
    change sigmaOneSuccessorSectionFormula.Evalb v ↔ _
    rw [hv]
    exact eval_sigmaOneSuccessorSectionFormula _ _ _ _ _ _⟩

instance sigmaOneSuccessorLiftFormula_defined :
    ℒₛₑₜ-function₃[V] successorForcingLift via sigmaOneSuccessorLiftFormula :=
  ⟨fun v ↦ by
    have hv : v = ![v 0, v 1, v 2, v 3] := by funext i; fin_cases i <;> rfl
    change sigmaOneSuccessorLiftFormula.Evalb v ↔ _
    rw [hv]
    exact eval_sigmaOneSuccessorLiftFormula _ _ _ _⟩

def piOneSuccessorProjectionFormula : SetTheorySemisentence 5 :=
  “G C π k i. ∀ D, !sigmaOneSuccessorProjectionFormula D C π k i → G = D”

def piOneSuccessorSectionFormula : SetTheorySemisentence 6 :=
  “G P E k t i. ∀ D, !sigmaOneSuccessorSectionFormula D P E k t i → G = D”

def piOneSuccessorLiftFormula : SetTheorySemisentence 4 :=
  “G C A L. ∀ D, !sigmaOneSuccessorLiftFormula D C A L → G = D”

theorem piOneSuccessorProjectionFormula_piOne : IsPiFormula 1 piOneSuccessorProjectionFormula :=
  .all (.or (sigmaOneSuccessorProjectionFormula_sigmaOne.subst _).neg (.bounded (.rel _ _)))

theorem piOneSuccessorSectionFormula_piOne : IsPiFormula 1 piOneSuccessorSectionFormula :=
  .all (.or (sigmaOneSuccessorSectionFormula_sigmaOne.subst _).neg (.bounded (.rel _ _)))

theorem piOneSuccessorLiftFormula_piOne : IsPiFormula 1 piOneSuccessorLiftFormula :=
  .all (.or (sigmaOneSuccessorLiftFormula_sigmaOne.subst _).neg (.bounded (.rel _ _)))

instance piOneSuccessorProjectionFormula_defined :
    ℒₛₑₜ-function₄[V] successorStageProjection via piOneSuccessorProjectionFormula :=
  ⟨fun v ↦ by simp [piOneSuccessorProjectionFormula]⟩

instance piOneSuccessorSectionFormula_defined :
    ℒₛₑₜ-function₅[V] successorStageSection via piOneSuccessorSectionFormula :=
  ⟨fun v ↦ by simp [piOneSuccessorSectionFormula]⟩

instance piOneSuccessorLiftFormula_defined :
    ℒₛₑₜ-function₃[V] successorForcingLift via piOneSuccessorLiftFormula :=
  ⟨fun v ↦ by simp [piOneSuccessorLiftFormula]⟩

end ZFVP
