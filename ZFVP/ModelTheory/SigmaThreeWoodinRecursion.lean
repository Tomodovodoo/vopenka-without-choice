import ZFVP.ModelTheory.SigmaThreeWoodinRecursionStep
import ZFVP.SetTheory.LocalRecursionCertificates

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
universe u

def woodinHistoryCertificate (φ : SetTheorySemisentence 2) : SetTheorySemisentence 2 :=
  “H θ. !(sigmaRecursionAttemptFormula φ) θ H”

def woodinHistoryPiCertificate (φ : SetTheorySemisentence 2) : SetTheorySemisentence 2 :=
  “H θ. ∀ G, !(woodinHistoryCertificate φ) G θ → H = G”

theorem woodinHistoryCertificate_sigmaThree {φ : SetTheorySemisentence 2}
    (hφ : IsSigmaFormula 3 φ) : IsSigmaFormula 3 (woodinHistoryCertificate φ) :=
  (sigmaRecursionAttemptFormula_sigma hφ).subst _

theorem woodinHistoryPiCertificate_piThree {φ : SetTheorySemisentence 2}
    (hφ : IsSigmaFormula 3 φ) : IsPiFormula 3 (woodinHistoryPiCertificate φ) :=
  .all (.or ((woodinHistoryCertificate_sigmaThree hφ).subst _).neg (.bounded (.rel _ _)))

variable {V : Type u} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem woodinIterationRec_eq_step_history (θ : V) [IsOrdinal θ] :
    woodinIterationRec θ = woodinIterationRecursionStep (woodinIterationHistory θ) := by
  rw [woodinIterationRec_rule]
  simp only [woodinIterationRecursionStep, woodinIterationHistory, domain_definableGraph,
    woodinIterationPrefix, woodinIterationCardinalPrefix]

theorem eval_woodinHistoryCertificate_of_prefix_definitions (φ : SetTheorySemisentence 2)
    (θ H : V) [IsOrdinal θ]
    (he : ∀ β ∈ θ, ∀ z : V, φ.Evalb ![z, woodinIterationHistory β] ↔ z = woodinIterationRec β) :
    (woodinHistoryCertificate φ).Evalb ![H, θ] ↔ H = woodinIterationHistory θ := by
  simpa [woodinHistoryCertificate, woodinIterationHistory, Semiformula.Evalb, Semiformula.eval_substs, Matrix.comp_vecCons',
    Matrix.constant_eq_singleton, Function.comp_def] using
    eval_sigmaRecursionAttemptFormula_of_prefix_definitions φ woodinIterationRec
      woodinIterationRec_definable θ H he

/-- Formulas for the actual recursive values and their entire history. Prefix
validity and the inverse forcing inputs are explicit remaining semantic requirements. -/
theorem woodinRecursion_deltaThree_on_prefixes_of_inverse_forcing :
    ∃ σ π σH πH : SetTheorySemisentence 2,
      IsSigmaFormula 3 σ ∧ IsPiFormula 3 π ∧ IsSigmaFormula 3 σH ∧ IsPiFormula 3 πH ∧
      ∀ (V : Type u) [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙], ∀ δ θ : V,
        IsOrdinal θ → IsWoodinSupercompact δ → θ ∈ δ →
        (∀ β ∈ succ θ, IsWoodinIteration δ β (woodinIterationPrefix β) (woodinIterationCardinalPrefix β)) →
        (∀ β ∈ succ θ, β ≠ ∅ → β ≠ succ (⋃ˢ β) →
          ¬IsChoicelessInaccessible (woodinLimitCardinal (woodinIterationCardinalPrefix β)) →
          ∀ p ∈ forcingInverseCodePoset β (woodinIterationPrefix β),
            p ∈ forcingFormula (forcingInverseCodePoset β (woodinIterationPrefix β))
              (forcingInverseCodeOrder β (woodinIterationPrefix β))
              (regularCardinalFormula.or limitOfRegularCardinalsFormula)
              (standardTuple ![checkName (forcingInverseCodeTop β (woodinIterationPrefix β))
                (woodinLimitCardinal (woodinIterationCardinalPrefix β))])) →
        (∀ β ∈ succ θ, β ≠ ∅ → β ≠ succ (⋃ˢ β) →
          ¬IsChoicelessInaccessible (woodinLimitCardinal (woodinIterationCardinalPrefix β)) →
          ∀ p ∈ forcingInverseCodePoset β (woodinIterationPrefix β),
            p ∈ forcingFormula (forcingInverseCodePoset β (woodinIterationPrefix β))
              (forcingInverseCodeOrder β (woodinIterationPrefix β)) dependentChoiceAtFormula
              (standardTuple ![checkName (forcingInverseCodeTop β (woodinIterationPrefix β))
                (woodinLimitCardinal (woodinIterationCardinalPrefix β))])) → ∀ z,
          (σ.Evalb ![z, θ] ↔ z = woodinIterationRec θ) ∧
          (π.Evalb ![z, θ] ↔ z = woodinIterationRec θ) ∧
          (σH.Evalb ![z, θ] ↔ z = woodinIterationHistory θ) ∧
          (πH.Evalb ![z, θ] ↔ z = woodinIterationHistory θ) := by
  obtain ⟨φ, _, hφ, _, heφ⟩ := woodinRecursionStep_deltaThree_on_history_of_inverse_forcing.{u}
  refine ⟨sigmaTransfiniteRecFormula φ, piTransfiniteRecFormula φ,
    woodinHistoryCertificate φ, woodinHistoryPiCertificate φ,
    sigmaTransfiniteRecFormula_sigma hφ, piTransfiniteRecFormula_pi hφ,
    woodinHistoryCertificate_sigmaThree hφ, woodinHistoryPiCertificate_piThree hφ, ?_⟩
  intro V _ _ _ δ θ hθ hδ hθδ hvalid hγ hDC z
  let := hθ
  let := hδ.inaccessible.1
  have he : ∀ β ∈ succ θ, ∀ w : V, φ.Evalb ![w, woodinIterationHistory β] ↔ w = woodinIterationRec β := by
    intro β hβ w
    let := IsOrdinal.of_mem hβ
    have hβδ : β ∈ δ := by
      rcases mem_succ_iff.mp hβ with rfl | hb
      · exact hθδ
      · exact IsOrdinal.toIsTransitive.mem_trans hb hθδ
    have hd : domain (woodinIterationHistory β) = β := domain_definableGraph _ _ _
    have hh := heφ V δ (woodinIterationHistory β)
    dsimp only at hh
    simp only [hd] at hh
    have hs := (hh inferInstance hδ hβδ (hvalid β hβ) (hγ β hβ) (hDC β hβ) w).1
    rwa [← woodinIterationRec_eq_step_history β] at hs
  have hrec := eval_sigmaTransfiniteRecFormula_of_prefix_definitions φ woodinIterationRec
    woodinIterationRec_definable θ
  have hhist := fun w ↦ eval_woodinHistoryCertificate_of_prefix_definitions φ θ w
    (fun β hb ↦ he β (mem_succ_iff.mpr (Or.inr hb)))
  have hR := fun w ↦ hrec w he
  refine ⟨hR z, ?_, hhist z, ?_⟩
  · simp only [Semiformula.Evalb] at hR
    simp [piTransfiniteRecFormula, Semiformula.eval_substs, Matrix.comp_vecCons',
      Matrix.constant_eq_singleton, Function.comp_def, hR]
  · simp only [Semiformula.Evalb] at hhist
    simp [woodinHistoryPiCertificate, Semiformula.eval_substs, Matrix.comp_vecCons',
      Matrix.constant_eq_singleton, Function.comp_def, hhist]

end ZFVP
