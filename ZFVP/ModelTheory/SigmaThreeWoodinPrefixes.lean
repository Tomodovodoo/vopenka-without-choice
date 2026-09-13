import ZFVP.ModelTheory.WoodinRecursionComplexity

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
universe u

def woodinIterationPrefixCertificate (Λ : SetTheorySemisentence 2) : SetTheorySemisentence 2 :=
  “z θ. ∃ H, !Λ H θ ∧ ∃ C, !sigmaOneWoodinHistoryCodesFormula C H ∧
    !sigmaOneForcingCodeUnionFormula z θ C”

def woodinIterationCardinalPrefixCertificate (Λ : SetTheorySemisentence 2) : SetTheorySemisentence 2 :=
  “z θ. ∃ H, !Λ H θ ∧ ∃ K, !sigmaOneWoodinHistoryCardinalsFormula K H ∧
    !sigmaOneWoodinHistoryCardinalUnionFormula z θ K”

theorem woodinIterationPrefixCertificate_sigmaThree {Λ : SetTheorySemisentence 2}
    (hΛ : IsSigmaFormula 3 Λ) : IsSigmaFormula 3 (woodinIterationPrefixCertificate Λ) :=
  .exs (.and (hΛ.subst _) (.exs (.and ((sigmaOneWoodinHistoryCodesFormula_sigmaOne.mono (by omega)).subst _)
    ((sigmaOneForcingCodeUnionFormula_sigmaOne.mono (by omega)).subst _))))

theorem woodinIterationCardinalPrefixCertificate_sigmaThree {Λ : SetTheorySemisentence 2}
    (hΛ : IsSigmaFormula 3 Λ) : IsSigmaFormula 3 (woodinIterationCardinalPrefixCertificate Λ) :=
  .exs (.and (hΛ.subst _) (.exs (.and ((sigmaOneWoodinHistoryCardinalsFormula_sigmaOne.mono (by omega)).subst _)
    ((sigmaOneWoodinHistoryCardinalUnionFormula_sigmaOne.mono (by omega)).subst _))))

variable {V : Type u} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem eval_woodinIterationPrefixCertificate (Λ : SetTheorySemisentence 2) (z θ : V)
    (he : ∀ H : V, Λ.Evalb ![H, θ] ↔ H = woodinIterationHistory θ) :
    (woodinIterationPrefixCertificate Λ).Evalb ![z, θ] ↔ z = woodinIterationPrefix θ := by
  simp only [Semiformula.Evalb] at he
  simp [woodinIterationPrefixCertificate, Semiformula.eval_substs, Matrix.comp_vecCons',
    Matrix.constant_eq_singleton, Function.comp_def, he, woodinIterationPrefix]

theorem eval_woodinIterationCardinalPrefixCertificate (Λ : SetTheorySemisentence 2) (z θ : V)
    (he : ∀ H : V, Λ.Evalb ![H, θ] ↔ H = woodinIterationHistory θ) :
    (woodinIterationCardinalPrefixCertificate Λ).Evalb ![z, θ] ↔ z = woodinIterationCardinalPrefix θ := by
  simp only [Semiformula.Evalb] at he
  simp [woodinIterationCardinalPrefixCertificate, Semiformula.eval_substs, Matrix.comp_vecCons',
    Matrix.constant_eq_singleton, Function.comp_def, he, woodinIterationCardinalPrefix]

/-- The actual forcing-prefix code and cardinal table have parameter-free uniform
Delta-three graphs below any Woodin supercompact cardinal. -/
theorem woodinIterationPrefixes_deltaThree_uniform :
    ∃ σ π σK πK : SetTheorySemisentence 2,
      IsSigmaFormula 3 σ ∧ IsPiFormula 3 π ∧ IsSigmaFormula 3 σK ∧ IsPiFormula 3 πK ∧
      ∀ (V : Type u) [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙], ∀ δ θ : V,
        IsWoodinSupercompact δ → θ ∈ δ → ∀ z,
          (σ.Evalb ![z, θ] ↔ z = woodinIterationPrefix θ) ∧
          (π.Evalb ![z, θ] ↔ z = woodinIterationPrefix θ) ∧
          (σK.Evalb ![z, θ] ↔ z = woodinIterationCardinalPrefix θ) ∧
          (πK.Evalb ![z, θ] ↔ z = woodinIterationCardinalPrefix θ) := by
  obtain ⟨_, _, Λ, _, _, _, hΛ, _, heΛ⟩ := woodinRecursion_deltaThree_uniform.{u}
  let σ := woodinIterationPrefixCertificate Λ
  let σK := woodinIterationCardinalPrefixCertificate Λ
  have hσ := woodinIterationPrefixCertificate_sigmaThree hΛ
  have hσK := woodinIterationCardinalPrefixCertificate_sigmaThree hΛ
  refine ⟨σ, woodinRecursionStepPiCertificate σ, σK, woodinRecursionStepPiCertificate σK,
    hσ, woodinRecursionStepPiCertificate_piThree hσ, hσK, woodinRecursionStepPiCertificate_piThree hσK, ?_⟩
  intro V _ _ _ δ θ hδ hθ z
  have he := fun H ↦ (heΛ V δ θ hδ hθ H).2.2.1
  have hp := fun w ↦ eval_woodinIterationPrefixCertificate Λ w θ he
  have hK := fun w ↦ eval_woodinIterationCardinalPrefixCertificate Λ w θ he
  refine ⟨hp z, ?_, hK z, ?_⟩
  · simp only [Semiformula.Evalb] at hp
    simp [woodinRecursionStepPiCertificate, Semiformula.eval_substs, Matrix.comp_vecCons',
      Matrix.constant_eq_singleton, Function.comp_def, σ, hp]
  · simp only [Semiformula.Evalb] at hK
    simp [woodinRecursionStepPiCertificate, Semiformula.eval_substs, Matrix.comp_vecCons',
      Matrix.constant_eq_singleton, Function.comp_def, σK, hK]

end ZFVP
