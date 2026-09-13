import ZFVP.ModelTheory.SigmaThreeWoodinStageRule
import ZFVP.ModelTheory.WoodinSuccessorComplexityOnIteration
import ZFVP.ModelTheory.WoodinInverseComplexityOnIteration

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
universe u

/-- Uniform stage-rule formulas, retaining the two unresolved inverse-forcing inputs
only when the inverse branch is selected. -/
theorem woodinStageRule_deltaThree_on_iteration_of_inverse_forcing :
    ∃ σ π : SetTheorySemisentence 4, IsSigmaFormula 3 σ ∧ IsPiFormula 3 π ∧
      ∀ (V : Type u) [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙], ∀ δ θ s K : V,
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
          (σ.Evalb ![z, θ, s, K] ↔ z = woodinStageRule θ s K) ∧
          (π.Evalb ![z, θ, s, K] ↔ z = woodinStageRule θ s K) := by
  obtain ⟨A, _, Ac, _, hA, _, hAc, _, heA⟩ := woodinInitialCode_deltaThree_uniform.{u}
  obtain ⟨B, _, Bc, _, hB, _, hBc, _, heB⟩ := woodinSuccessorStage_deltaThree_on_iteration.{u}
  obtain ⟨I, _, Ic, _, hI, _, hIc, _, heI⟩ := woodinInverseStage_deltaThree_on_iteration.{u}
  let a := woodinInitialOutputCertificate A Ac
  let b := woodinPairedOutputCertificate B Bc
  let i := woodinPairedOutputCertificate I Ic
  let σ := woodinStageRuleCertificate a b sigmaTwoWoodinDirectOutputFormula i
  have hσ : IsSigmaFormula 3 σ := woodinStageRuleCertificate_sigmaThree
    (woodinInitialOutputCertificate_sigmaThree hA hAc)
    (woodinPairedOutputCertificate_sigmaThree hB hBc)
    sigmaTwoWoodinDirectOutputFormula_sigmaTwo.raise
    (woodinPairedOutputCertificate_sigmaThree hI hIc)
  refine ⟨σ, woodinInversePiCertificate σ, hσ, woodinInversePiCertificate_piThree hσ, ?_⟩
  intro V _ _ _ δ θ s K hθ hδ hθδ h hγ hDC z
  let := hθ
  have he : ∀ w : V, σ.Evalb ![w, θ, s, K] ↔ w = woodinStageRule θ s K := by
    intro w
    apply eval_woodinStageRuleCertificate
    · intro _
      exact eval_woodinInitialOutputCertificate A Ac _ _ w
        (fun C ↦ (heA V ⟨δ, hδ⟩ C).1) (fun L ↦ (heA V ⟨δ, hδ⟩ L).2.2.1)
    · intro _ hs
      have hk : ⋃ˢ θ ∈ θ := (congrArg (fun x : V ↦ (⋃ˢ θ) ∈ x) hs).mpr (mem_succ_self (⋃ˢ θ))
      have ho := IsOrdinal.of_mem hk
      have hh : IsWoodinIteration δ (succ (⋃ˢ θ)) s K := hs ▸ h
      exact eval_woodinPairedOutputCertificate B Bc _ _ _ _ _ w
        (fun C ↦ (heB V δ (⋃ˢ θ) s K ho hδ hh C).1)
        (fun L ↦ (heB V δ (⋃ˢ θ) s K ho hδ hh L).2.2.1)
    · intro _ _ _
      simp [sigmaTwoWoodinDirectOutputFormula]
    · intro hz hs hi
      have h0 : (∅ : V) ∈ θ := (IsOrdinal.subset_iff.mp (empty_subset θ)).resolve_left
        (fun heq ↦ hz heq.symm)
      exact eval_woodinPairedOutputCertificate I Ic _ _ _ _ _ w
        (fun C ↦ (heI V δ θ s K hθ h hδ hθδ h0 (hγ hz hs hi) (hDC hz hs hi) C).1)
        (fun L ↦ (heI V δ θ s K hθ h hδ hθδ h0 (hγ hz hs hi) (hDC hz hs hi) L).2.2.1)
  refine ⟨he z, ?_⟩
  simp only [Semiformula.Evalb] at he
  simp [woodinInversePiCertificate, Semiformula.eval_substs, Matrix.comp_vecCons',
    Matrix.constant_eq_singleton, Function.comp_def, he]

end ZFVP
