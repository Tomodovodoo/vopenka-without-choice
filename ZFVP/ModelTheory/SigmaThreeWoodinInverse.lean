import ZFVP.ModelTheory.SigmaThreeInverseSourceCutoff
import ZFVP.ModelTheory.DeltaTwoInverseTwoStepCode

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
universe u

def selectedWoodinInverseCertificate (Λ : SetTheorySemisentence 4) (Ξ Ω : SetTheorySemisentence 6)
    (φ : BoundedFormulaTree 3) : SetTheorySemisentence 4 :=
  “z θ s K. ∃ P, !sigmaTwoInverseCodePosetFormula P θ s ∧
    ∃ R, !sigmaTwoInverseCodeOrderFormula R θ s ∧ ∃ o, !sigmaOneInverseCodeTopFormula o θ s ∧
    ∃ γ, !sigmaOneWoodinLimitCardinalFormula γ K ∧ ∃ c, !Λ c θ s γ ∧
    ∃ Q, !Ξ Q P R o γ c ∧ ∃ S, !Ω S P R o γ c ∧ ∃ u, !boundedEmptyFormula u ∧
    !(sigmaTwoInverseTwoStepCodeCertificate φ) z θ s Q S u”

theorem selectedWoodinInverseCertificate_sigmaThree {Λ : SetTheorySemisentence 4}
    {Ξ Ω : SetTheorySemisentence 6} (hΛ : IsSigmaFormula 3 Λ)
    (hΞ : IsSigmaFormula 3 Ξ) (hΩ : IsSigmaFormula 3 Ω) (φ : BoundedFormulaTree 3) :
    IsSigmaFormula 3 (selectedWoodinInverseCertificate Λ Ξ Ω φ) :=
  .exs (.and (sigmaTwoInverseCodePosetFormula_sigmaTwo.raise.subst _)
    (.exs (.and (sigmaTwoInverseCodeOrderFormula_sigmaTwo.raise.subst _)
      (.exs (.and ((sigmaOneInverseCodeTopFormula_sigmaOne.mono (by omega)).subst _)
        (.exs (.and ((sigmaOneWoodinLimitCardinalFormula_sigmaOne.mono (by omega)).subst _)
          (.exs (.and (hΛ.subst _) (.exs (.and (hΞ.subst _) (.exs (.and (hΩ.subst _)
            (.exs (.and (.bounded (boundedEmptyFormula_bounded.subst _))
              ((sigmaTwoInverseTwoStepCodeCertificate_sigmaTwo φ).raise.subst _))))))))))))))))

def woodinInversePiCertificate (Λ : SetTheorySemisentence 4) : SetTheorySemisentence 4 :=
  “z θ s K. ∀ w, !Λ w θ s K → z = w”

theorem woodinInversePiCertificate_piThree {Λ : SetTheorySemisentence 4}
    (hΛ : IsSigmaFormula 3 Λ) : IsPiFormula 3 (woodinInversePiCertificate Λ) :=
  .all (.or (hΛ.subst _).neg (.bounded (.rel _ _)))

variable {V : Type u} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem eval_selectedWoodinInverseCertificate (Λ : SetTheorySemisentence 4) (Ξ Ω : SetTheorySemisentence 6)
    (φ : BoundedFormulaTree 3) (hφ : φ.formula = boundedPairMemberFormula) (z θ s K : V)
    (hΛ : ∀ c : V, Λ.Evalb ![c, θ, s, woodinLimitCardinal K] ↔
      c = forcingInverseSourceCutoff θ s (woodinLimitCardinal K))
    (hΞ : ∀ Q : V, Ξ.Evalb ![Q, forcingInverseCodePoset θ s, forcingInverseCodeOrder θ s,
      forcingInverseCodeTop θ s, woodinLimitCardinal K, forcingInverseSourceCutoff θ s (woodinLimitCardinal K)] ↔
      Q = saturatedHartogsPosetName (forcingInverseCodePoset θ s) (forcingInverseCodeOrder θ s)
        (forcingInverseCodeTop θ s) (woodinLimitCardinal K) (forcingInverseSourceCutoff θ s (woodinLimitCardinal K)))
    (hΩ : ∀ S : V, Ω.Evalb ![S, forcingInverseCodePoset θ s, forcingInverseCodeOrder θ s,
      forcingInverseCodeTop θ s, woodinLimitCardinal K, forcingInverseSourceCutoff θ s (woodinLimitCardinal K)] ↔
      S = saturatedHartogsOrderName (forcingInverseCodePoset θ s) (forcingInverseCodeOrder θ s)
        (forcingInverseCodeTop θ s) (woodinLimitCardinal K) (forcingInverseSourceCutoff θ s (woodinLimitCardinal K)))
    (hR : IsForcingPreorder (forcingInverseCodePoset θ s) (forcingInverseCodeOrder θ s))
    (hI : IsForcingIterand (forcingInverseCodePoset θ s) (forcingInverseCodeOrder θ s)
      (saturatedHartogsPosetName (forcingInverseCodePoset θ s) (forcingInverseCodeOrder θ s)
        (forcingInverseCodeTop θ s) (woodinLimitCardinal K) (forcingInverseSourceCutoff θ s (woodinLimitCardinal K)))
      (saturatedHartogsOrderName (forcingInverseCodePoset θ s) (forcingInverseCodeOrder θ s)
        (forcingInverseCodeTop θ s) (woodinLimitCardinal K) (forcingInverseSourceCutoff θ s (woodinLimitCardinal K))) ∅) :
    (selectedWoodinInverseCertificate Λ Ξ Ω φ).Evalb ![z, θ, s, K] ↔ z = woodinInverseSourceCode θ s K := by
  have he := eval_sigmaTwoInverseTwoStepCodeCertificate φ hφ hR hI
  simp only [Semiformula.Evalb] at hΛ hΞ hΩ he
  change _ ↔ z = forcingInverseTwoStepCode θ s
    (saturatedHartogsPosetName (forcingInverseCodePoset θ s) (forcingInverseCodeOrder θ s)
      (forcingInverseCodeTop θ s) (woodinLimitCardinal K) (forcingInverseSourceCutoff θ s (woodinLimitCardinal K)))
    (saturatedHartogsOrderName (forcingInverseCodePoset θ s) (forcingInverseCodeOrder θ s)
      (forcingInverseCodeTop θ s) (woodinLimitCardinal K) (forcingInverseSourceCutoff θ s (woodinLimitCardinal K))) ∅
  simp [selectedWoodinInverseCertificate, Semiformula.eval_substs, Matrix.comp_vecCons',
    Matrix.constant_eq_singleton, Function.comp_def, hΛ, hΞ, hΩ, he]

theorem eval_woodinInversePiCertificate (Λ : SetTheorySemisentence 4) (z θ s K : V)
    (he : ∀ w : V, Λ.Evalb ![w, θ, s, K] ↔ w = woodinInverseSourceCode θ s K) :
    (woodinInversePiCertificate Λ).Evalb ![z, θ, s, K] ↔ z = woodinInverseSourceCode θ s K := by
  simp only [Semiformula.Evalb] at he
  simp [woodinInversePiCertificate, Semiformula.eval_substs, Matrix.comp_vecCons',
    Matrix.constant_eq_singleton, Function.comp_def, he]

theorem woodinInverseSourceCode_sigmaThree_uniform :
    ∃ Λ : SetTheorySemisentence 4, IsSigmaFormula 3 Λ ∧
      ∀ (V : Type u) [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙], ∀ θ s K : V,
        let P := forcingInverseCodePoset θ s;
        let R := forcingInverseCodeOrder θ s;
        let o := forcingInverseCodeTop θ s;
        let γ := woodinLimitCardinal K;
        let τ := forcingInverseHartogsName θ s γ;
        IsForcingPreorder P R → IsForcingTop P R o →
        (∀ p ∈ P, p ∈ forcingFormula P R regularCardinalFormula (standardTuple ![τ])) →
        (∃ d, IsWoodinNamedPrefixCutoff P R o γ τ d) → ∀ z,
          (Λ.Evalb ![z, θ, s, K] ↔ z = woodinInverseSourceCode θ s K) := by
  obtain ⟨Λ, hΛ, heΛ⟩ := forcingInverseSourceCutoff_sigmaThree_uniform.{u}
  obtain ⟨Ξ, hΞ, heΞ⟩ := saturatedHartogsPosetName_sigmaThree_uniform.{u}
  obtain ⟨Ω, hΩ, heΩ⟩ := saturatedHartogsOrderName_sigmaThree_uniform.{u}
  obtain ⟨φ, hφ⟩ := boundedFormulaTree_exists boundedPairMemberFormula_bounded
  refine ⟨selectedWoodinInverseCertificate Λ Ξ Ω φ, selectedWoodinInverseCertificate_sigmaThree hΛ hΞ hΩ φ, ?_⟩
  intro V _ _ _ θ s K
  dsimp only
  intro hR ht hreg hex z
  obtain ⟨d, hd⟩ := hex
  have hleast := forcingInverseSourceCutoff_spec hd
  apply eval_selectedWoodinInverseCertificate Λ Ξ Ω φ hφ z θ s K
  · exact heΛ V θ s (woodinLimitCardinal K) hR ht hreg ⟨d, hd⟩
  · intro Q
    exact heΞ V Q _ _ _ _ _ hR ht hleast.1
  · intro S
    exact heΩ V S _ _ _ _ _ hR ht hleast.1
  · exact hR
  · exact saturatedHartogsCollapse_iterand hR ht hleast.2.1.2.1 hreg

theorem woodinInverseSourceCode_deltaThree_uniform :
    ∃ Λ Ξ : SetTheorySemisentence 4, IsSigmaFormula 3 Λ ∧ IsPiFormula 3 Ξ ∧
      ∀ (V : Type u) [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙], ∀ θ s K : V,
        let P := forcingInverseCodePoset θ s;
        let R := forcingInverseCodeOrder θ s;
        let o := forcingInverseCodeTop θ s;
        let γ := woodinLimitCardinal K;
        let τ := forcingInverseHartogsName θ s γ;
        IsForcingPreorder P R → IsForcingTop P R o →
        (∀ p ∈ P, p ∈ forcingFormula P R regularCardinalFormula (standardTuple ![τ])) →
        (∃ d, IsWoodinNamedPrefixCutoff P R o γ τ d) → ∀ z,
          (Λ.Evalb ![z, θ, s, K] ↔ z = woodinInverseSourceCode θ s K) ∧
          (Ξ.Evalb ![z, θ, s, K] ↔ z = woodinInverseSourceCode θ s K) := by
  obtain ⟨Λ, hΛ, he⟩ := woodinInverseSourceCode_sigmaThree_uniform.{u}
  refine ⟨Λ, woodinInversePiCertificate Λ, hΛ, woodinInversePiCertificate_piThree hΛ, ?_⟩
  intro V _ _ _ θ s K
  dsimp only
  intro hR ht hreg hex z
  exact ⟨he V θ s K hR ht hreg hex z, eval_woodinInversePiCertificate Λ z θ s K (he V θ s K hR ht hreg hex)⟩

end ZFVP
