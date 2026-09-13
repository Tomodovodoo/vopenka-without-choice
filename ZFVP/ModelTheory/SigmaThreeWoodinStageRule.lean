import ZFVP.ModelTheory.SigmaThreeWoodinInitialCode
import ZFVP.ModelTheory.SigmaThreeWoodinCardinalNext
import ZFVP.ModelTheory.SigmaThreeWoodinInverse
import ZFVP.ModelTheory.WoodinStageRule
import ZFVP.SetTheory.PiOneRegularInaccessible

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
universe u

/-- Combine the forcing-code and cardinal-table graphs into the stage output. -/
def woodinPairedOutputCertificate (Λ Ξ : SetTheorySemisentence 4) : SetTheorySemisentence 4 :=
  “z θ s K. ∃ C, !Λ C θ s K ∧ ∃ L, !Ξ L θ s K ∧ !boundedKpairFormula z C L”

theorem woodinPairedOutputCertificate_sigmaThree {Λ Ξ : SetTheorySemisentence 4}
    (hΛ : IsSigmaFormula 3 Λ) (hΞ : IsSigmaFormula 3 Ξ) :
    IsSigmaFormula 3 (woodinPairedOutputCertificate Λ Ξ) :=
  .exs (.and (hΛ.subst _) (.exs (.and (hΞ.subst _) (.bounded (boundedKpairFormula_bounded.subst _)))))

def woodinInitialOutputCertificate (Λ Ξ : SetTheorySemisentence 1) : SetTheorySemisentence 1 :=
  “z. ∃ C, !Λ C ∧ ∃ L, !Ξ L ∧ !boundedKpairFormula z C L”

theorem woodinInitialOutputCertificate_sigmaThree {Λ Ξ : SetTheorySemisentence 1}
    (hΛ : IsSigmaFormula 3 Λ) (hΞ : IsSigmaFormula 3 Ξ) :
    IsSigmaFormula 3 (woodinInitialOutputCertificate Λ Ξ) :=
  .exs (.and (hΛ.subst _) (.exs (.and (hΞ.subst _) (.bounded (boundedKpairFormula_bounded.subst _)))))

def sigmaTwoWoodinDirectOutputFormula : SetTheorySemisentence 4 :=
  “z θ s K. ∃ C, !sigmaTwoForcingDirectCodeFormula C θ s ∧
    ∃ γ, !sigmaOneWoodinLimitCardinalFormula γ K ∧
    ∃ L, !sigmaOneFamilyNextFormula L θ K γ ∧ !boundedKpairFormula z C L”

theorem sigmaTwoWoodinDirectOutputFormula_sigmaTwo : IsSigmaFormula 2 sigmaTwoWoodinDirectOutputFormula :=
  .exs (.and (sigmaTwoForcingDirectCodeFormula_sigmaTwo.subst _)
    (.exs (.and (sigmaOneWoodinLimitCardinalFormula_sigmaOne.raise.subst _)
      (.exs (.and (sigmaOneFamilyNextFormula_sigmaOne.raise.subst _)
        (.bounded (boundedKpairFormula_bounded.subst _)))))))

/-- This uses exactly the zero, successor and inaccessibility tests of `woodinStageRule`. -/
def woodinStageRuleCertificate (A : SetTheorySemisentence 1)
    (B D I : SetTheorySemisentence 4) : SetTheorySemisentence 4 :=
  “z θ s K. ∃ k, !boundedSUnionFormula k θ ∧
    ∃ γ, !sigmaOneWoodinLimitCardinalFormula γ K ∧
    ((!boundedEmptyFormula θ ∧ !A z) ∨
      (¬!boundedEmptyFormula θ ∧
        ((!boundedSuccFormula θ k ∧ !B z k s K) ∨
          (¬!boundedSuccFormula θ k ∧
            ((!rankCriterionFormula γ ∧ !D z θ s K) ∨
              (¬!rankCriterionFormula γ ∧ !I z θ s K))))))”

theorem woodinStageRuleCertificate_sigmaThree {A : SetTheorySemisentence 1}
    {B D I : SetTheorySemisentence 4} (hA : IsSigmaFormula 3 A)
    (hB : IsSigmaFormula 3 B) (hD : IsSigmaFormula 3 D) (hI : IsSigmaFormula 3 I) :
    IsSigmaFormula 3 (woodinStageRuleCertificate A B D I) :=
  .exs (.and (.bounded (boundedSUnionFormula_bounded.subst _))
    (.exs (.and ((sigmaOneWoodinLimitCardinalFormula_sigmaOne.mono (by omega)).subst _)
      (.or (.and (.bounded (boundedEmptyFormula_bounded.subst _)) (hA.subst _))
        (.and (.bounded (boundedEmptyFormula_bounded.subst _).neg)
          (.or (.and (.bounded (boundedSuccFormula_bounded.subst _)) (hB.subst _))
            (.and (.bounded (boundedSuccFormula_bounded.subst _).neg)
              (.or (.and ((rankCriterionFormula_piOne.raise.mono (by omega)).subst _) (hD.subst _))
                (.and ((rankCriterionFormula_piOne.neg.mono (by omega)).subst _) (hI.subst _))))))))))

variable {V : Type u} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem eval_woodinPairedOutputCertificate (Λ Ξ : SetTheorySemisentence 4) (θ s K C L z : V)
    (hΛ : ∀ w : V, Λ.Evalb ![w, θ, s, K] ↔ w = C)
    (hΞ : ∀ w : V, Ξ.Evalb ![w, θ, s, K] ↔ w = L) :
    (woodinPairedOutputCertificate Λ Ξ).Evalb ![z, θ, s, K] ↔ z = ⟨C, L⟩ₖ := by
  simp only [Semiformula.Evalb] at hΛ hΞ
  simp [woodinPairedOutputCertificate, Semiformula.eval_substs, Matrix.comp_vecCons',
    Matrix.constant_eq_singleton, Function.comp_def, hΛ, hΞ]

theorem eval_woodinInitialOutputCertificate (Λ Ξ : SetTheorySemisentence 1) (C L z : V)
    (hΛ : ∀ w : V, Λ.Evalb ![w] ↔ w = C)
    (hΞ : ∀ w : V, Ξ.Evalb ![w] ↔ w = L) :
    (woodinInitialOutputCertificate Λ Ξ).Evalb ![z] ↔ z = ⟨C, L⟩ₖ := by
  simp only [Semiformula.Evalb] at hΛ hΞ
  simp [woodinInitialOutputCertificate, Semiformula.eval_substs, Matrix.comp_vecCons',
    Matrix.constant_eq_singleton, Function.comp_def, hΛ, hΞ]

instance sigmaTwoWoodinDirectOutputFormula_defined :
    ℒₛₑₜ-function₃[V] (fun θ s K ↦ ⟨forcingDirectCode θ s,
      forcingFamilyNext θ K (woodinLimitCardinal K)⟩ₖ) via sigmaTwoWoodinDirectOutputFormula :=
  ⟨fun v ↦ by simp [sigmaTwoWoodinDirectOutputFormula]⟩

theorem eval_woodinStageRuleCertificate (A : SetTheorySemisentence 1)
    (B D I : SetTheorySemisentence 4) (θ s K z : V)
    (hA : θ = ∅ → (A.Evalb ![z] ↔ z = ⟨woodinInitialCode, woodinInitialCardinals⟩ₖ))
    (hB : θ ≠ ∅ → θ = succ (⋃ˢ θ) → (B.Evalb ![z, ⋃ˢ θ, s, K] ↔
      z = ⟨woodinIterationSuccessor (⋃ˢ θ) s K, woodinIterationCardinalNext (⋃ˢ θ) s K⟩ₖ))
    (hD : θ ≠ ∅ → θ ≠ succ (⋃ˢ θ) → IsChoicelessInaccessible (woodinLimitCardinal K) →
      (D.Evalb ![z, θ, s, K] ↔ z = ⟨forcingDirectCode θ s, forcingFamilyNext θ K (woodinLimitCardinal K)⟩ₖ))
    (hI : θ ≠ ∅ → θ ≠ succ (⋃ˢ θ) → ¬IsChoicelessInaccessible (woodinLimitCardinal K) →
      (I.Evalb ![z, θ, s, K] ↔ z = ⟨woodinInverseSourceCode θ s K, woodinInverseCardinalNext θ s K⟩ₖ)) :
    (woodinStageRuleCertificate A B D I).Evalb ![z, θ, s, K] ↔ z = woodinStageRule θ s K := by
  simp only [Semiformula.Evalb] at hA hB hD hI
  simp [woodinStageRuleCertificate, Semiformula.eval_substs, Matrix.comp_vecCons',
    Matrix.constant_eq_singleton, Function.comp_def, rankCriterionHeight_iff_choicelessInaccessible]
  simp only [← not_isEmpty_iff_isNonempty, isEmpty_iff_eq_empty]
  classical
  unfold woodinStageRule
  split_ifs with hz hs hi
  · simpa only [iff_true_intro hz, not_true_eq_false, true_and, false_and, or_false] using hA hz
  · simpa only [iff_false_intro hz, iff_true_intro hs, not_false_eq_true, not_true_eq_false,
      false_and, true_and, false_or, or_false] using hB hz hs
  · simpa only [iff_false_intro hz, iff_false_intro hs, iff_true_intro hi, not_false_eq_true,
      not_true_eq_false, false_and, true_and, false_or, or_false] using hD hz hs hi
  · simpa only [iff_false_intro hz, iff_false_intro hs, iff_false_intro hi, not_false_eq_true,
      false_and, true_and, false_or] using hI hz hs hi

end ZFVP
