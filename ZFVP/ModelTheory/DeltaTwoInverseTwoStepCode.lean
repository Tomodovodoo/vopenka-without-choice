import ZFVP.ModelTheory.DeltaOneTwoStepColumns
import ZFVP.ModelTheory.DeltaOneTwoStepOrder
import ZFVP.ModelTheory.DeltaTwoForcingLimitCodes

set_option maxRecDepth 8192
set_option maxHeartbeats 800000

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

def sigmaTwoInverseTwoStepCodeCertificate (φ : BoundedFormulaTree 3) : SetTheorySemisentence 6 :=
  “z θ s Q S u. ∃ P, !sigmaOneForcingCodePFormula P s ∧
    ∃ R, !sigmaOneForcingCodeRFormula R s ∧
    ∃ π, !sigmaOneForcingCodeπFormula π s ∧
    ∃ E, !sigmaOneForcingCodeEFormula E s ∧
    ∃ L, !sigmaOneForcingCodeLFormula L s ∧
    ∃ t, !sigmaOneForcingCodetFormula t s ∧
    ∃ U, !sigmaOneForcingCodeUniverseFormula U s ∧
    ∃ C, !piOneInverseLimitGraphFormula C θ P π U ∧
    ∃ T, !sigmaOneThreadOrderGraphFormula T θ R C ∧
    ∃ D, !sigmaOneTwoStepConditionSetFormula D C T Q u ∧
    ∃ W, !(sigmaOneTwoStepOrderSetFormula φ) W C T Q S u ∧
    ∃ ρ, !boundedLimitProjectionColumnFormula ρ θ C ∧
    ∃ F, !sigmaOneLimitSectionColumnFormula F θ P π E ∧
    ∃ M, !sigmaOneLimitLiftColumnFormula M C θ P π L ∧
    ∃ p, !sigmaOneTwoStepProjectionFormula p C T Q u ∧
    ∃ e, !sigmaOneTwoStepSectionFormula e C u ∧
    ∃ r, !sigmaOneComposeProjectionColumnFormula r θ ρ p ∧
    ∃ f, !sigmaOneComposeSectionColumnFormula f θ F e ∧
    ∃ m, !sigmaOneTwoStepLiftColumnFormula m θ D P M ∧
    ∃ o, !boundedEmptyFormula o ∧
    ∃ a, !boundedValueFormula a t o ∧
    ∃ one, !sigmaOneSectionThreadFormula one θ π E o a ∧
    ∃ v, !boundedKpairFormula v one u ∧
    !sigmaOneForcingCodeNextFormula z θ s D W r f m v”

theorem sigmaTwoInverseTwoStepCodeCertificate_sigmaTwo (φ : BoundedFormulaTree 3) :
    IsSigmaFormula 2 (sigmaTwoInverseTwoStepCodeCertificate φ) :=
  .exs (.and (.raise ((sigmaOneForcingCodePFormula_sigmaOne).subst _))
    (.exs (.and (.raise ((sigmaOneForcingCodeRFormula_sigmaOne).subst _))
    (.exs (.and (.raise ((sigmaOneForcingCodeπFormula_sigmaOne).subst _))
    (.exs (.and (.raise ((sigmaOneForcingCodeEFormula_sigmaOne).subst _))
    (.exs (.and (.raise ((sigmaOneForcingCodeLFormula_sigmaOne).subst _))
    (.exs (.and (.raise ((sigmaOneForcingCodetFormula_sigmaOne).subst _))
    (.exs (.and (.raise ((sigmaOneForcingCodeUniverseFormula_sigmaOne).subst _))
    (.exs (.and (.raise ((piOneInverseLimitGraphFormula_piOne).subst _))
    (.exs (.and (.raise ((sigmaOneThreadOrderGraphFormula_sigmaOne).subst _))
    (.exs (.and (.raise ((sigmaOneTwoStepConditionSetFormula_sigmaOne).subst _))
    (.exs (.and (.raise ((sigmaOneTwoStepOrderSetFormula_sigmaOne φ).subst _))
    (.exs (.and (.bounded ((boundedLimitProjectionColumnFormula_bounded).subst _))
    (.exs (.and (.raise ((sigmaOneLimitSectionColumnFormula_sigmaOne).subst _))
    (.exs (.and (.raise ((sigmaOneLimitLiftColumnFormula_sigmaOne).subst _))
    (.exs (.and (.raise ((sigmaOneTwoStepProjectionFormula_sigmaOne).subst _))
    (.exs (.and (.raise ((sigmaOneTwoStepSectionFormula_sigmaOne).subst _))
    (.exs (.and (.raise ((sigmaOneComposeProjectionColumnFormula_sigmaOne).subst _))
    (.exs (.and (.raise ((sigmaOneComposeSectionColumnFormula_sigmaOne).subst _))
    (.exs (.and (.raise ((sigmaOneTwoStepLiftColumnFormula_sigmaOne).subst _))
    (.exs (.and (.bounded ((boundedEmptyFormula_bounded).subst _))
    (.exs (.and (.bounded ((boundedValueFormula_bounded).subst _))
    (.exs (.and (.raise ((sigmaOneSectionThreadFormula_sigmaOne).subst _))
    (.exs (.and (.bounded ((boundedKpairFormula_bounded).subst _))
    (.raise (sigmaOneForcingCodeNextFormula_sigmaOne.subst _)))))))))))))))))))))))))))))))))))))))))))))))

def piTwoInverseTwoStepCodeCertificate (φ : BoundedFormulaTree 3) : SetTheorySemisentence 6 :=
  “z θ s Q S u. ∀ w, !(sigmaTwoInverseTwoStepCodeCertificate φ) w θ s Q S u → z = w”

theorem piTwoInverseTwoStepCodeCertificate_piTwo (φ : BoundedFormulaTree 3) :
    IsPiFormula 2 (piTwoInverseTwoStepCodeCertificate φ) :=
  .all (.or ((sigmaTwoInverseTwoStepCodeCertificate_sigmaTwo φ).subst _).neg (.bounded (.rel _ _)))

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem eval_sigmaTwoInverseTwoStepCodeCertificate (φ : BoundedFormulaTree 3)
    (hφ : φ.formula = boundedPairMemberFormula) {θ s Q S u : V}
    (hR : IsForcingPreorder (forcingInverseLimit θ (forcingCodeP s) (forcingCodeπ s) (forcingCodeUniverse s))
      (forcingThreadOrder θ (forcingCodeR s) (forcingInverseLimit θ (forcingCodeP s) (forcingCodeπ s) (forcingCodeUniverse s))))
    (h : IsForcingIterand (forcingInverseLimit θ (forcingCodeP s) (forcingCodeπ s) (forcingCodeUniverse s))
      (forcingThreadOrder θ (forcingCodeR s) (forcingInverseLimit θ (forcingCodeP s) (forcingCodeπ s) (forcingCodeUniverse s))) Q S u) (z : V) :
    (sigmaTwoInverseTwoStepCodeCertificate φ).Evalb ![z, θ, s, Q, S, u] ↔
      z = forcingInverseTwoStepCode θ s Q S u := by
  have he := eval_sigmaOneTwoStepOrderSetFormula φ hφ hR h
  simp only [Semiformula.Evalb] at he
  simp [sigmaTwoInverseTwoStepCodeCertificate, Semiformula.eval_substs, Matrix.comp_vecCons',
    Matrix.constant_eq_singleton, Function.comp_def, he, forcingInverseTwoStepCode, forcingTwoStepColumnCode]

theorem eval_piTwoInverseTwoStepCodeCertificate (φ : BoundedFormulaTree 3)
    (hφ : φ.formula = boundedPairMemberFormula) {θ s Q S u : V}
    (hR : IsForcingPreorder (forcingInverseLimit θ (forcingCodeP s) (forcingCodeπ s) (forcingCodeUniverse s))
      (forcingThreadOrder θ (forcingCodeR s) (forcingInverseLimit θ (forcingCodeP s) (forcingCodeπ s) (forcingCodeUniverse s))))
    (h : IsForcingIterand (forcingInverseLimit θ (forcingCodeP s) (forcingCodeπ s) (forcingCodeUniverse s))
      (forcingThreadOrder θ (forcingCodeR s) (forcingInverseLimit θ (forcingCodeP s) (forcingCodeπ s) (forcingCodeUniverse s))) Q S u) (z : V) :
    (piTwoInverseTwoStepCodeCertificate φ).Evalb ![z, θ, s, Q, S, u] ↔
      z = forcingInverseTwoStepCode θ s Q S u := by
  have he := eval_sigmaTwoInverseTwoStepCodeCertificate φ hφ hR h
  simp only [Semiformula.Evalb] at he
  simp [piTwoInverseTwoStepCodeCertificate, Semiformula.eval_substs, Matrix.comp_vecCons',
    Matrix.constant_eq_singleton, Function.comp_def, he]

theorem forcingInverseTwoStepCode_deltaTwo_formulas :
    ∃ σ π : SetTheorySemisentence 6, IsSigmaFormula 2 σ ∧ IsPiFormula 2 π ∧
      ∀ θ s Q S u : V,
        IsForcingPreorder (forcingInverseLimit θ (forcingCodeP s) (forcingCodeπ s) (forcingCodeUniverse s))
          (forcingThreadOrder θ (forcingCodeR s) (forcingInverseLimit θ (forcingCodeP s) (forcingCodeπ s) (forcingCodeUniverse s))) →
        IsForcingIterand (forcingInverseLimit θ (forcingCodeP s) (forcingCodeπ s) (forcingCodeUniverse s))
          (forcingThreadOrder θ (forcingCodeR s) (forcingInverseLimit θ (forcingCodeP s) (forcingCodeπ s) (forcingCodeUniverse s))) Q S u → ∀ z,
        (σ.Evalb ![z, θ, s, Q, S, u] ↔ z = forcingInverseTwoStepCode θ s Q S u) ∧
        (π.Evalb ![z, θ, s, Q, S, u] ↔ z = forcingInverseTwoStepCode θ s Q S u) := by
  obtain ⟨φ, hφ⟩ := boundedFormulaTree_exists boundedPairMemberFormula_bounded
  exact ⟨sigmaTwoInverseTwoStepCodeCertificate φ, piTwoInverseTwoStepCodeCertificate φ,
    sigmaTwoInverseTwoStepCodeCertificate_sigmaTwo φ, piTwoInverseTwoStepCodeCertificate_piTwo φ,
    fun _ _ _ _ _ hR h z ↦ ⟨eval_sigmaTwoInverseTwoStepCodeCertificate φ hφ hR h z,
      eval_piTwoInverseTwoStepCodeCertificate φ hφ hR h z⟩⟩

end ZFVP
