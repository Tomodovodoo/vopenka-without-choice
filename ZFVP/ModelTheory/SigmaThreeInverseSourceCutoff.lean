import ZFVP.ModelTheory.DeltaTwoInverseComponents
import ZFVP.ModelTheory.SigmaThreeSaturatedHartogsNames
import ZFVP.SetTheory.PiTwoNamedPrefixCutoff

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
universe u

def inverseSourceCutoffCertificate (Λ : SetTheorySemisentence 6) (Ξ : SetTheorySemisentence 5) :
    SetTheorySemisentence 4 :=
  “δ θ s γ. ∃ P, !sigmaTwoInverseCodePosetFormula P θ s ∧
    ∃ R, !sigmaTwoInverseCodeOrderFormula R θ s ∧ ∃ o, !sigmaOneInverseCodeTopFormula o θ s ∧
    ∃ τ, !Ξ τ P R o γ ∧ !Λ P R o γ τ δ”

theorem inverseSourceCutoffCertificate_sigmaThree {Λ : SetTheorySemisentence 6} {Ξ : SetTheorySemisentence 5}
    (hΛ : IsSigmaFormula 3 Λ) (hΞ : IsSigmaFormula 3 Ξ) : IsSigmaFormula 3 (inverseSourceCutoffCertificate Λ Ξ) :=
  .exs (.and (sigmaTwoInverseCodePosetFormula_sigmaTwo.raise.subst _)
    (.exs (.and (sigmaTwoInverseCodeOrderFormula_sigmaTwo.raise.subst _)
      (.exs (.and ((sigmaOneInverseCodeTopFormula_sigmaOne.mono (by omega)).subst _)
        (.exs (.and (hΞ.subst _) (hΛ.subst _))))))))

def inverseCutoffPiCertificate (Λ : SetTheorySemisentence 4) : SetTheorySemisentence 4 :=
  “δ θ s γ. ∀ d, !Λ d θ s γ → δ = d”

theorem inverseCutoffPiCertificate_piThree {Λ : SetTheorySemisentence 4}
    (hΛ : IsSigmaFormula 3 Λ) : IsPiFormula 3 (inverseCutoffPiCertificate Λ) :=
  .all (.or (hΛ.subst _).neg (.bounded (.rel _ _)))

variable {V : Type u} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem eval_inverseSourceCutoffCertificate (Λ : SetTheorySemisentence 6) (Ξ : SetTheorySemisentence 5)
    (δ θ s γ : V)
    (hΞ : ∀ τ : V, Ξ.Evalb ![τ, forcingInverseCodePoset θ s, forcingInverseCodeOrder θ s,
      forcingInverseCodeTop θ s, γ] ↔ τ = forcingInverseHartogsName θ s γ)
    (hΛ : Λ.Evalb ![forcingInverseCodePoset θ s, forcingInverseCodeOrder θ s,
      forcingInverseCodeTop θ s, γ, forcingInverseHartogsName θ s γ, δ] ↔ δ = forcingInverseSourceCutoff θ s γ) :
    (inverseSourceCutoffCertificate Λ Ξ).Evalb ![δ, θ, s, γ] ↔ δ = forcingInverseSourceCutoff θ s γ := by
  simp only [Semiformula.Evalb] at hΞ hΛ
  simp [inverseSourceCutoffCertificate, Semiformula.eval_substs, Matrix.comp_vecCons',
    Matrix.constant_eq_singleton, Function.comp_def, hΞ, hΛ]

theorem eval_inverseCutoffPiCertificate (Λ : SetTheorySemisentence 4) (δ θ s γ : V)
    (he : ∀ d : V, Λ.Evalb ![d, θ, s, γ] ↔ d = forcingInverseSourceCutoff θ s γ) :
    (inverseCutoffPiCertificate Λ).Evalb ![δ, θ, s, γ] ↔ δ = forcingInverseSourceCutoff θ s γ := by
  simp only [Semiformula.Evalb] at he
  simp [inverseCutoffPiCertificate, Semiformula.eval_substs, Matrix.comp_vecCons',
    Matrix.constant_eq_singleton, Function.comp_def, he]

theorem forcingInverseSourceCutoff_sigmaThree_uniform :
    ∃ Λ : SetTheorySemisentence 4, IsSigmaFormula 3 Λ ∧
      ∀ (V : Type u) [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙], ∀ θ s γ : V,
        let P := forcingInverseCodePoset θ s;
        let R := forcingInverseCodeOrder θ s;
        let o := forcingInverseCodeTop θ s;
        let τ := forcingInverseHartogsName θ s γ;
        IsForcingPreorder P R → IsForcingTop P R o →
        (∀ p ∈ P, p ∈ forcingFormula P R regularCardinalFormula (standardTuple ![τ])) →
        (∃ d, IsWoodinNamedPrefixCutoff P R o γ τ d) → ∀ δ,
          (Λ.Evalb ![δ, θ, s, γ] ↔ δ = forcingInverseSourceCutoff θ s γ) := by
  obtain ⟨Λ, hΛ, heΛ⟩ := leastWoodinNamedPrefixCutoff_deltaThree_uniform.{u}
  obtain ⟨Ξ, hΞ, heΞ⟩ := checkedHartogsName_sigmaThree_uniform.{u}
  refine ⟨inverseSourceCutoffCertificate Λ Ξ, inverseSourceCutoffCertificate_sigmaThree (hΛ .sigma) hΞ, ?_⟩
  intro V _ _ _ θ s γ
  dsimp only
  intro hR ht hreg hex δ
  apply eval_inverseSourceCutoffCertificate Λ Ξ δ θ s γ
  · intro τ
    exact heΞ V τ _ _ _ γ hR ht
  · exact (heΛ V _ _ _ γ _ δ hR ht (hartogsNumberName_isName _ _ _)
      (fun p hp ↦ forces_zeroMember_of_regular hR ht hp
        ⟨forcingInverseHartogsName θ s γ, hartogsNumberName_isName _ _ _⟩ (hreg p hp))).trans
      (woodinNamedPrefixCutoff_eq_iff_least_of_exists hex).symm

theorem forcingInverseSourceCutoff_deltaThree_uniform :
    ∃ Λ Ξ : SetTheorySemisentence 4, IsSigmaFormula 3 Λ ∧ IsPiFormula 3 Ξ ∧
      ∀ (V : Type u) [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙], ∀ θ s γ : V,
        let P := forcingInverseCodePoset θ s;
        let R := forcingInverseCodeOrder θ s;
        let o := forcingInverseCodeTop θ s;
        let τ := forcingInverseHartogsName θ s γ;
        IsForcingPreorder P R → IsForcingTop P R o →
        (∀ p ∈ P, p ∈ forcingFormula P R regularCardinalFormula (standardTuple ![τ])) →
        (∃ d, IsWoodinNamedPrefixCutoff P R o γ τ d) → ∀ δ,
          (Λ.Evalb ![δ, θ, s, γ] ↔ δ = forcingInverseSourceCutoff θ s γ) ∧
          (Ξ.Evalb ![δ, θ, s, γ] ↔ δ = forcingInverseSourceCutoff θ s γ) := by
  obtain ⟨Λ, hΛ, he⟩ := forcingInverseSourceCutoff_sigmaThree_uniform.{u}
  refine ⟨Λ, inverseCutoffPiCertificate Λ, hΛ, inverseCutoffPiCertificate_piThree hΛ, ?_⟩
  intro V _ _ _ θ s γ
  dsimp only
  intro hR ht hreg hex δ
  exact ⟨he V θ s γ hR ht hreg hex δ, eval_inverseCutoffPiCertificate Λ δ θ s γ (he V θ s γ hR ht hreg hex)⟩

end ZFVP
