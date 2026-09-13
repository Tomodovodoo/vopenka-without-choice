import ZFVP.ModelTheory.SigmaThreeWoodinInverse

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
universe u

def inverseCardinalNextCertificate (Λ : SetTheorySemisentence 4) : SetTheorySemisentence 4 :=
  “z θ s K. ∃ γ, !sigmaOneWoodinLimitCardinalFormula γ K ∧
    ∃ c, !Λ c θ s γ ∧ !sigmaOneFamilyNextFormula z θ K c”

theorem inverseCardinalNextCertificate_sigmaThree {Λ : SetTheorySemisentence 4}
    (hΛ : IsSigmaFormula 3 Λ) : IsSigmaFormula 3 (inverseCardinalNextCertificate Λ) :=
  .exs (.and ((sigmaOneWoodinLimitCardinalFormula_sigmaOne.mono (by omega)).subst _)
    (.exs (.and (hΛ.subst _) ((sigmaOneFamilyNextFormula_sigmaOne.mono (by omega)).subst _))))

def inverseCardinalNextPiCertificate (Λ : SetTheorySemisentence 4) : SetTheorySemisentence 4 :=
  “z θ s K. ∀ w, !Λ w θ s K → z = w”

theorem inverseCardinalNextPiCertificate_piThree {Λ : SetTheorySemisentence 4}
    (hΛ : IsSigmaFormula 3 Λ) : IsPiFormula 3 (inverseCardinalNextPiCertificate Λ) :=
  .all (.or (hΛ.subst _).neg (.bounded (.rel _ _)))

variable {V : Type u} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem eval_inverseCardinalNextCertificate (Λ : SetTheorySemisentence 4) (z θ s K : V)
    (he : ∀ c : V, Λ.Evalb ![c, θ, s, woodinLimitCardinal K] ↔
      c = forcingInverseSourceCutoff θ s (woodinLimitCardinal K)) :
    (inverseCardinalNextCertificate Λ).Evalb ![z, θ, s, K] ↔ z = woodinInverseCardinalNext θ s K := by
  simp only [Semiformula.Evalb] at he
  simp [inverseCardinalNextCertificate, Semiformula.eval_substs, Matrix.comp_vecCons',
    Matrix.constant_eq_singleton, Function.comp_def, he, woodinInverseCardinalNext]

theorem eval_inverseCardinalNextPiCertificate (Λ : SetTheorySemisentence 4) (z θ s K : V)
    (he : ∀ w : V, Λ.Evalb ![w, θ, s, K] ↔ w = woodinInverseCardinalNext θ s K) :
    (inverseCardinalNextPiCertificate Λ).Evalb ![z, θ, s, K] ↔ z = woodinInverseCardinalNext θ s K := by
  simp only [Semiformula.Evalb] at he
  simp [inverseCardinalNextPiCertificate, Semiformula.eval_substs, Matrix.comp_vecCons',
    Matrix.constant_eq_singleton, Function.comp_def, he]

theorem woodinInverseCardinalNext_deltaThree_uniform :
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
          (Λ.Evalb ![z, θ, s, K] ↔ z = woodinInverseCardinalNext θ s K) ∧
          (Ξ.Evalb ![z, θ, s, K] ↔ z = woodinInverseCardinalNext θ s K) := by
  obtain ⟨Λ, hΛ, heΛ⟩ := forcingInverseSourceCutoff_sigmaThree_uniform.{u}
  refine ⟨inverseCardinalNextCertificate Λ, inverseCardinalNextPiCertificate (inverseCardinalNextCertificate Λ),
    inverseCardinalNextCertificate_sigmaThree hΛ,
    inverseCardinalNextPiCertificate_piThree (inverseCardinalNextCertificate_sigmaThree hΛ), ?_⟩
  intro V _ _ _ θ s K
  dsimp only
  intro hR ht hreg hex z
  have he (w : V) := eval_inverseCardinalNextCertificate Λ w θ s K
    (heΛ V θ s (woodinLimitCardinal K) hR ht hreg hex)
  exact ⟨he z, eval_inverseCardinalNextPiCertificate _ z θ s K he⟩

end ZFVP
