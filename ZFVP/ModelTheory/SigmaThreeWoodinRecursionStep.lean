import ZFVP.ModelTheory.WoodinStageRuleComplexityOnIteration
import ZFVP.ModelTheory.DeltaOneForcingCodeUnion
import ZFVP.ModelTheory.DeltaOneWoodinHistoryTables

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
universe u

def woodinRecursionStepCertificate (Λ : SetTheorySemisentence 4) : SetTheorySemisentence 2 :=
  “z H. ∃ θ, !boundedRelationDomainFormula θ H ∧
    ∃ C, !sigmaOneWoodinHistoryCodesFormula C H ∧
    ∃ L, !sigmaOneWoodinHistoryCardinalsFormula L H ∧
    ∃ s, !sigmaOneForcingCodeUnionFormula s θ C ∧
    ∃ K, !sigmaOneWoodinHistoryCardinalUnionFormula K θ L ∧ !Λ z θ s K”

theorem woodinRecursionStepCertificate_sigmaThree {Λ : SetTheorySemisentence 4}
    (hΛ : IsSigmaFormula 3 Λ) : IsSigmaFormula 3 (woodinRecursionStepCertificate Λ) :=
  .exs (.and (.bounded (boundedRelationDomainFormula_bounded.subst _))
    (.exs (.and ((sigmaOneWoodinHistoryCodesFormula_sigmaOne.mono (by omega)).subst _)
      (.exs (.and ((sigmaOneWoodinHistoryCardinalsFormula_sigmaOne.mono (by omega)).subst _)
        (.exs (.and ((sigmaOneForcingCodeUnionFormula_sigmaOne.mono (by omega)).subst _)
          (.exs (.and ((sigmaOneWoodinHistoryCardinalUnionFormula_sigmaOne.mono (by omega)).subst _)
            (hΛ.subst _))))))))))

def woodinRecursionStepPiCertificate (Λ : SetTheorySemisentence 2) : SetTheorySemisentence 2 :=
  “z H. ∀ w, !Λ w H → z = w”

theorem woodinRecursionStepPiCertificate_piThree {Λ : SetTheorySemisentence 2}
    (hΛ : IsSigmaFormula 3 Λ) : IsPiFormula 3 (woodinRecursionStepPiCertificate Λ) :=
  .all (.or (hΛ.subst _).neg (.bounded (.rel _ _)))

variable {V : Type u} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem eval_woodinRecursionStepCertificate (Λ : SetTheorySemisentence 4) (H z : V)
    (he : Λ.Evalb ![z, domain H,
      forcingIterationCodeUnion (domain H) (woodinHistoryCodes H),
      woodinHistoryCardinalUnion (domain H) (woodinHistoryCardinals H)] ↔
      z = woodinIterationRecursionStep H) :
    (woodinRecursionStepCertificate Λ).Evalb ![z, H] ↔ z = woodinIterationRecursionStep H := by
  simpa [woodinRecursionStepCertificate, Semiformula.eval_substs, Matrix.comp_vecCons',
    Matrix.constant_eq_singleton, Function.comp_def] using he

/-- All complexity bounds are uniform; the semantic hypotheses concern the actual
aggregate of the supplied history, including the conditional inverse requirements. -/
theorem woodinRecursionStep_deltaThree_on_history_of_inverse_forcing :
    ∃ σ π : SetTheorySemisentence 2, IsSigmaFormula 3 σ ∧ IsPiFormula 3 π ∧
      ∀ (V : Type u) [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙], ∀ δ H : V,
        let θ := domain H;
        let s := forcingIterationCodeUnion θ (woodinHistoryCodes H);
        let K := woodinHistoryCardinalUnion θ (woodinHistoryCardinals H);
        IsOrdinal θ → IsWoodinSupercompact δ → θ ∈ δ → IsWoodinIteration δ θ s K →
        (θ ≠ ∅ → θ ≠ succ (⋃ˢ θ) → ¬IsChoicelessInaccessible (woodinLimitCardinal K) →
          ∀ p ∈ forcingInverseCodePoset θ s,
            p ∈ forcingFormula (forcingInverseCodePoset θ s) (forcingInverseCodeOrder θ s)
              (regularCardinalFormula.or limitOfRegularCardinalsFormula)
              (standardTuple ![checkName (forcingInverseCodeTop θ s) (woodinLimitCardinal K)])) →
        (θ ≠ ∅ → θ ≠ succ (⋃ˢ θ) → ¬IsChoicelessInaccessible (woodinLimitCardinal K) →
          ∀ p ∈ forcingInverseCodePoset θ s,
            p ∈ forcingFormula (forcingInverseCodePoset θ s) (forcingInverseCodeOrder θ s)
              dependentChoiceAtFormula
              (standardTuple ![checkName (forcingInverseCodeTop θ s) (woodinLimitCardinal K)])) → ∀ z,
          (σ.Evalb ![z, H] ↔ z = woodinIterationRecursionStep H) ∧
          (π.Evalb ![z, H] ↔ z = woodinIterationRecursionStep H) := by
  obtain ⟨Λ, _, hΛ, _, heΛ⟩ := woodinStageRule_deltaThree_on_iteration_of_inverse_forcing.{u}
  let σ := woodinRecursionStepCertificate Λ
  have hσ := woodinRecursionStepCertificate_sigmaThree hΛ
  refine ⟨σ, woodinRecursionStepPiCertificate σ, hσ, woodinRecursionStepPiCertificate_piThree hσ, ?_⟩
  intro V _ _ _ δ H
  dsimp only
  intro hθ hδ hθδ h hγ hDC z
  have he : ∀ w : V, σ.Evalb ![w, H] ↔ w = woodinIterationRecursionStep H := by
    intro w
    exact eval_woodinRecursionStepCertificate Λ H w
      (heΛ V δ _ _ _ hθ hδ hθδ h hγ hDC w).1
  refine ⟨he z, ?_⟩
  simp only [Semiformula.Evalb] at he
  simp [woodinRecursionStepPiCertificate, Semiformula.eval_substs, Matrix.comp_vecCons',
    Matrix.constant_eq_singleton, Function.comp_def, he]

end ZFVP
