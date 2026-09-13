import ZFVP.ModelTheory.DeltaOneTwoStepOrder
import ZFVP.ModelTheory.DeltaOneSuccessorColumns
import ZFVP.ModelTheory.DeltaOneForcingCodeNext

set_option maxRecDepth 4096

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

def sigmaOneSuccessorCodeCertificate (φ : BoundedFormulaTree 3) : SetTheorySemisentence 6 :=
  “z k s Q S u. ∃ Pt, !sigmaOneForcingCodePFormula Pt s ∧
    ∃ Rt, !sigmaOneForcingCodeRFormula Rt s ∧
    ∃ P, !boundedValueFormula P Pt k ∧
    ∃ R, !boundedValueFormula R Rt k ∧
    ∃ C, !sigmaOneTwoStepConditionSetFormula C P R Q u ∧
    ∃ T, !(sigmaOneTwoStepOrderSetFormula φ) T P R Q S u ∧
    ∃ π, !sigmaOneForcingCodeπFormula π s ∧
    ∃ E, !sigmaOneForcingCodeEFormula E s ∧
    ∃ L, !sigmaOneForcingCodeLFormula L s ∧
    ∃ t, !sigmaOneForcingCodetFormula t s ∧
    ∃ θ, !boundedSuccFormula θ k ∧
    ∃ ρ, !sigmaOneSuccessorProjectionColumnFormula ρ θ C π k ∧
    ∃ F, !sigmaOneSuccessorSectionColumnFormula F θ Pt E k u ∧
    ∃ M, !sigmaOneSuccessorLiftColumnFormula M θ C Pt L k ∧
    ∃ o, !boundedValueFormula o t k ∧
    ∃ v, !boundedKpairFormula v o u ∧
    !sigmaOneForcingCodeNextFormula z θ s C T ρ F M v”

theorem sigmaOneSuccessorCodeCertificate_sigmaOne (φ : BoundedFormulaTree 3) :
    IsSigmaFormula 1 (sigmaOneSuccessorCodeCertificate φ) :=
  .exs (.and (sigmaOneForcingCodePFormula_sigmaOne.subst _)
    (.exs (.and (sigmaOneForcingCodeRFormula_sigmaOne.subst _)
    (.exs (.and (.bounded (boundedValueFormula_bounded.subst _))
    (.exs (.and (.bounded (boundedValueFormula_bounded.subst _))
    (.exs (.and (sigmaOneTwoStepConditionSetFormula_sigmaOne.subst _)
    (.exs (.and ((sigmaOneTwoStepOrderSetFormula_sigmaOne φ).subst _)
    (.exs (.and (sigmaOneForcingCodeπFormula_sigmaOne.subst _)
    (.exs (.and (sigmaOneForcingCodeEFormula_sigmaOne.subst _)
    (.exs (.and (sigmaOneForcingCodeLFormula_sigmaOne.subst _)
    (.exs (.and (sigmaOneForcingCodetFormula_sigmaOne.subst _)
    (.exs (.and (.bounded (boundedSuccFormula_bounded.subst _))
    (.exs (.and (sigmaOneSuccessorProjectionColumnFormula_sigmaOne.subst _)
    (.exs (.and (sigmaOneSuccessorSectionColumnFormula_sigmaOne.subst _)
    (.exs (.and (sigmaOneSuccessorLiftColumnFormula_sigmaOne.subst _)
    (.exs (.and (.bounded (boundedValueFormula_bounded.subst _))
    (.exs (.and (.bounded (boundedKpairFormula_bounded.subst _))
    (sigmaOneForcingCodeNextFormula_sigmaOne.subst _))))))))))))))))))))))))))))))))

def piOneSuccessorCodeCertificate (φ : BoundedFormulaTree 3) : SetTheorySemisentence 6 :=
  “z k s Q S u. ∀ w, !(sigmaOneSuccessorCodeCertificate φ) w k s Q S u → z = w”

theorem piOneSuccessorCodeCertificate_piOne (φ : BoundedFormulaTree 3) :
    IsPiFormula 1 (piOneSuccessorCodeCertificate φ) :=
  .all (.or ((sigmaOneSuccessorCodeCertificate_sigmaOne φ).subst _).neg (.bounded (.rel _ _)))

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem eval_sigmaOneSuccessorCodeCertificate (φ : BoundedFormulaTree 3)
    (hφ : φ.formula = boundedPairMemberFormula) {k s Q S u : V}
    (hR : IsForcingPreorder ((forcingCodeP s) ‘ k) ((forcingCodeR s) ‘ k))
    (h : IsForcingIterand ((forcingCodeP s) ‘ k) ((forcingCodeR s) ‘ k) Q S u) (z : V) :
    (sigmaOneSuccessorCodeCertificate φ).Evalb ![z, k, s, Q, S, u] ↔ z = forcingSuccessorCode k s Q S u := by
  have he := eval_sigmaOneTwoStepOrderSetFormula φ hφ hR h
  simp only [Semiformula.Evalb] at he
  simp [sigmaOneSuccessorCodeCertificate, Semiformula.eval_substs, Matrix.comp_vecCons',
    Matrix.constant_eq_singleton, Function.comp_def, he, forcingSuccessorCode]

theorem eval_piOneSuccessorCodeCertificate (φ : BoundedFormulaTree 3)
    (hφ : φ.formula = boundedPairMemberFormula) {k s Q S u : V}
    (hR : IsForcingPreorder ((forcingCodeP s) ‘ k) ((forcingCodeR s) ‘ k))
    (h : IsForcingIterand ((forcingCodeP s) ‘ k) ((forcingCodeR s) ‘ k) Q S u) (z : V) :
    (piOneSuccessorCodeCertificate φ).Evalb ![z, k, s, Q, S, u] ↔ z = forcingSuccessorCode k s Q S u := by
  have he := eval_sigmaOneSuccessorCodeCertificate φ hφ hR h
  simp only [Semiformula.Evalb] at he
  simp [piOneSuccessorCodeCertificate, Semiformula.eval_substs, Matrix.comp_vecCons',
    Matrix.constant_eq_singleton, Function.comp_def, he]

theorem forcingSuccessorCode_deltaOne_formulas :
    ∃ σ π : SetTheorySemisentence 6, IsSigmaFormula 1 σ ∧ IsPiFormula 1 π ∧
      ∀ k s Q S u : V, IsForcingPreorder ((forcingCodeP s) ‘ k) ((forcingCodeR s) ‘ k) →
        IsForcingIterand ((forcingCodeP s) ‘ k) ((forcingCodeR s) ‘ k) Q S u → ∀ z,
        (σ.Evalb ![z, k, s, Q, S, u] ↔ z = forcingSuccessorCode k s Q S u) ∧
        (π.Evalb ![z, k, s, Q, S, u] ↔ z = forcingSuccessorCode k s Q S u) := by
  obtain ⟨φ, hφ⟩ := boundedFormulaTree_exists boundedPairMemberFormula_bounded
  exact ⟨sigmaOneSuccessorCodeCertificate φ, piOneSuccessorCodeCertificate φ,
    sigmaOneSuccessorCodeCertificate_sigmaOne φ, piOneSuccessorCodeCertificate_piOne φ,
    fun _ _ _ _ _ hR h z ↦ ⟨eval_sigmaOneSuccessorCodeCertificate φ hφ hR h z,
      eval_piOneSuccessorCodeCertificate φ hφ hR h z⟩⟩

end ZFVP
