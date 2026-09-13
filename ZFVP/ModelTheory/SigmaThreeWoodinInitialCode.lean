import ZFVP.ModelTheory.SigmaThreeWoodinInitialStage
import ZFVP.ModelTheory.DeltaOneInitialCode

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
universe u

def woodinInitialCodeCertificate (Λ : SetTheorySemisentence 1) : SetTheorySemisentence 1 :=
  “z. ∃ x, !Λ x ∧ ∃ P, !sigmaOneWoodinStagePosetFormula P x ∧
    ∃ R, !sigmaOneWoodinStageOrderFormula R x ∧ ∃ o, !sigmaOneWoodinStageTopFormula o x ∧
    !sigmaOneForcingInitialCodeFormula z P R o”

def woodinInitialCardinalsCertificate (Λ : SetTheorySemisentence 1) : SetTheorySemisentence 1 :=
  “z. ∃ x, !Λ x ∧ ∃ κ, !sigmaOneWoodinStageCardinalFormula κ x ∧
    ∃ e, !boundedEmptyFormula e ∧ !sigmaOneFamilyNextFormula z e e κ”

theorem woodinInitialCodeCertificate_sigmaThree {Λ : SetTheorySemisentence 1}
    (hΛ : IsSigmaFormula 3 Λ) : IsSigmaFormula 3 (woodinInitialCodeCertificate Λ) :=
  .exs (.and (hΛ.subst _) (.exs (.and ((sigmaOneWoodinStagePosetFormula_sigmaOne.mono (by omega)).subst _)
    (.exs (.and ((sigmaOneWoodinStageOrderFormula_sigmaOne.mono (by omega)).subst _)
      (.exs (.and ((sigmaOneWoodinStageTopFormula_sigmaOne.mono (by omega)).subst _)
        ((sigmaOneForcingInitialCodeFormula_sigmaOne.mono (by omega)).subst _))))))))

theorem woodinInitialCardinalsCertificate_sigmaThree {Λ : SetTheorySemisentence 1}
    (hΛ : IsSigmaFormula 3 Λ) : IsSigmaFormula 3 (woodinInitialCardinalsCertificate Λ) :=
  .exs (.and (hΛ.subst _) (.exs (.and ((sigmaOneWoodinStageCardinalFormula_sigmaOne.mono (by omega)).subst _)
    (.exs (.and (.bounded (boundedEmptyFormula_bounded.subst _))
      ((sigmaOneFamilyNextFormula_sigmaOne.mono (by omega)).subst _))))))

variable {V : Type u} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem eval_woodinInitialCodeCertificate (Λ : SetTheorySemisentence 1) (z : V)
    (he : ∀ x : V, Λ.Evalb ![x] ↔ x = woodinInitialStage) :
    (woodinInitialCodeCertificate Λ).Evalb ![z] ↔ z = woodinInitialCode := by
  simp only [Semiformula.Evalb] at he
  simp [woodinInitialCodeCertificate, Semiformula.eval_substs, Matrix.comp_vecCons',
    Matrix.constant_eq_singleton, Function.comp_def, he, woodinInitialCode]

theorem eval_woodinInitialCardinalsCertificate (Λ : SetTheorySemisentence 1) (z : V)
    (he : ∀ x : V, Λ.Evalb ![x] ↔ x = woodinInitialStage) :
    (woodinInitialCardinalsCertificate Λ).Evalb ![z] ↔ z = woodinInitialCardinals := by
  simp only [Semiformula.Evalb] at he
  simp [woodinInitialCardinalsCertificate, Semiformula.eval_substs, Matrix.comp_vecCons',
    Matrix.constant_eq_singleton, Function.comp_def, he, woodinInitialCardinals]

omit [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] in
theorem eval_initialOutputPiCertificate (Λ : SetTheorySemisentence 1) (z a : V)
    (he : ∀ x : V, Λ.Evalb ![x] ↔ x = a) :
    (initialStagePiCertificate Λ).Evalb ![z] ↔ z = a := by
  simp only [Semiformula.Evalb] at he
  simp [initialStagePiCertificate, Semiformula.eval_substs, Matrix.comp_vecCons',
    Matrix.constant_eq_singleton, Function.comp_def, he]

theorem woodinInitialCode_deltaThree_uniform :
    ∃ σ π σc πc : SetTheorySemisentence 1,
      IsSigmaFormula 3 σ ∧ IsPiFormula 3 π ∧ IsSigmaFormula 3 σc ∧ IsPiFormula 3 πc ∧
      ∀ (V : Type u) [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙],
        (∃ δ : V, IsWoodinSupercompact δ) → ∀ z : V,
          (σ.Evalb ![z] ↔ z = woodinInitialCode) ∧ (π.Evalb ![z] ↔ z = woodinInitialCode) ∧
          (σc.Evalb ![z] ↔ z = woodinInitialCardinals) ∧ (πc.Evalb ![z] ↔ z = woodinInitialCardinals) := by
  obtain ⟨Λ, hΛ, he⟩ := woodinInitialStage_sigmaThree_uniform.{u}
  let σ := woodinInitialCodeCertificate Λ
  let σc := woodinInitialCardinalsCertificate Λ
  have hσ := woodinInitialCodeCertificate_sigmaThree hΛ
  have hσc := woodinInitialCardinalsCertificate_sigmaThree hΛ
  refine ⟨σ, initialStagePiCertificate σ, σc, initialStagePiCertificate σc,
    hσ, initialStagePiCertificate_piThree hσ, hσc, initialStagePiCertificate_piThree hσc, ?_⟩
  intro V _ _ _ hδ z
  have hC := fun x ↦ eval_woodinInitialCodeCertificate Λ x (he V hδ)
  have hK := fun x ↦ eval_woodinInitialCardinalsCertificate Λ x (he V hδ)
  exact ⟨hC z, eval_initialOutputPiCertificate σ z _ hC, hK z, eval_initialOutputPiCertificate σc z _ hK⟩

end ZFVP
