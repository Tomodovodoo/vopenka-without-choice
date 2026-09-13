import ZFVP.ModelTheory.SigmaThreeWoodinSuccessor

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
universe u

def iterationCutoffCertificate (Λ : SetTheorySemisentence 5) : SetTheorySemisentence 4 :=
  “δ k s K. ∃ Pt, !sigmaOneForcingCodePFormula Pt s ∧
    ∃ Rt, !sigmaOneForcingCodeRFormula Rt s ∧ ∃ ot, !sigmaOneForcingCodetFormula ot s ∧
    ∃ P, !boundedValueFormula P Pt k ∧ ∃ R, !boundedValueFormula R Rt k ∧
    ∃ o, !boundedValueFormula o ot k ∧ ∃ κ, !boundedValueFormula κ K k ∧ !Λ P R o κ δ”

theorem iterationCutoffCertificate_sigmaThree {Λ : SetTheorySemisentence 5}
    (hΛ : IsSigmaFormula 3 Λ) : IsSigmaFormula 3 (iterationCutoffCertificate Λ) :=
  .exs (.and ((sigmaOneForcingCodePFormula_sigmaOne.mono (by omega)).subst _)
    (.exs (.and ((sigmaOneForcingCodeRFormula_sigmaOne.mono (by omega)).subst _)
      (.exs (.and ((sigmaOneForcingCodetFormula_sigmaOne.mono (by omega)).subst _)
        (.exs (.and (.bounded (boundedValueFormula_bounded.subst _))
          (.exs (.and (.bounded (boundedValueFormula_bounded.subst _))
            (.exs (.and (.bounded (boundedValueFormula_bounded.subst _))
              (.exs (.and (.bounded (boundedValueFormula_bounded.subst _)) (hΛ.subst _))))))))))))))

def woodinCardinalNextCertificate (Λ : SetTheorySemisentence 5) : SetTheorySemisentence 4 :=
  “z k s K. ∃ δ, !(iterationCutoffCertificate Λ) δ k s K ∧
    ∃ θ, !boundedSuccFormula θ k ∧ !sigmaOneFamilyNextFormula z θ K δ”

theorem woodinCardinalNextCertificate_sigmaThree {Λ : SetTheorySemisentence 5}
    (hΛ : IsSigmaFormula 3 Λ) : IsSigmaFormula 3 (woodinCardinalNextCertificate Λ) :=
  .exs (.and ((iterationCutoffCertificate_sigmaThree hΛ).subst _)
    (.exs (.and (.bounded (boundedSuccFormula_bounded.subst _))
      ((sigmaOneFamilyNextFormula_sigmaOne.mono (by omega)).subst _))))

def woodinCardinalNextPiCertificate (Λ : SetTheorySemisentence 4) : SetTheorySemisentence 4 :=
  “z k s K. ∀ w, !Λ w k s K → z = w”

theorem woodinCardinalNextPiCertificate_piThree {Λ : SetTheorySemisentence 4}
    (hΛ : IsSigmaFormula 3 Λ) : IsPiFormula 3 (woodinCardinalNextPiCertificate Λ) :=
  .all (.or (hΛ.subst _).neg (.bounded (.rel _ _)))

variable {V : Type u} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem eval_iterationCutoffCertificate (Λ : SetTheorySemisentence 5) (δ k s K : V) :
    (iterationCutoffCertificate Λ).Evalb ![δ, k, s, K] ↔
      Λ.Evalb ![(forcingCodeP s) ‘ k, (forcingCodeR s) ‘ k, (forcingCodet s) ‘ k, K ‘ k, δ] := by
  simp [iterationCutoffCertificate, Semiformula.eval_substs, Matrix.comp_vecCons',
    Matrix.constant_eq_singleton, Function.comp_def, Semiformula.Evalb]

theorem eval_woodinCardinalNextCertificate (Λ : SetTheorySemisentence 5) (z k s K : V)
    (he : ∀ δ : V,
      Λ.Evalb ![(forcingCodeP s) ‘ k, (forcingCodeR s) ‘ k, (forcingCodet s) ‘ k, K ‘ k, δ] ↔
        δ = woodinPrefixCutoff ((forcingCodeP s) ‘ k) ((forcingCodeR s) ‘ k) ((forcingCodet s) ‘ k) (K ‘ k)) :
    (woodinCardinalNextCertificate Λ).Evalb ![z, k, s, K] ↔ z = woodinIterationCardinalNext k s K := by
  have hc := fun δ : V ↦ (eval_iterationCutoffCertificate Λ δ k s K).trans (he δ)
  simp only [Semiformula.Evalb] at hc
  simp [woodinCardinalNextCertificate, Semiformula.eval_substs, Matrix.comp_vecCons',
    Matrix.constant_eq_singleton, Function.comp_def, hc, woodinIterationCardinalNext,
    woodinIterationStage, woodinSuccessorStep, woodinSuccessorAt]

theorem eval_woodinCardinalNextPiCertificate (Λ : SetTheorySemisentence 4) (z k s K : V)
    (he : ∀ w : V, Λ.Evalb ![w, k, s, K] ↔ w = woodinIterationCardinalNext k s K) :
    (woodinCardinalNextPiCertificate Λ).Evalb ![z, k, s, K] ↔ z = woodinIterationCardinalNext k s K := by
  simp only [Semiformula.Evalb] at he
  simp [woodinCardinalNextPiCertificate, Semiformula.eval_substs, Matrix.comp_vecCons',
    Matrix.constant_eq_singleton, Function.comp_def, he]

theorem woodinIterationCardinalNext_deltaThree_uniform :
    ∃ Λ Ξ : SetTheorySemisentence 4, IsSigmaFormula 3 Λ ∧ IsPiFormula 3 Ξ ∧
      ∀ (V : Type u) [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙], ∀ k s K : V,
        let P := (forcingCodeP s) ‘ k;
        let R := (forcingCodeR s) ‘ k;
        let o := (forcingCodet s) ‘ k;
        let κ := K ‘ k;
        IsForcingPreorder P R → IsForcingTop P R o → (∅ : V) ∈ κ →
        (∃ δ, IsWoodinPrefixCutoff P R o κ δ) → ∀ z,
          (Λ.Evalb ![z, k, s, K] ↔ z = woodinIterationCardinalNext k s K) ∧
          (Ξ.Evalb ![z, k, s, K] ↔ z = woodinIterationCardinalNext k s K) := by
  obtain ⟨Λ, hΛ, heΛ⟩ := leastWoodinPrefixCutoff_deltaThree_uniform.{u}
  refine ⟨woodinCardinalNextCertificate Λ, woodinCardinalNextPiCertificate (woodinCardinalNextCertificate Λ),
    woodinCardinalNextCertificate_sigmaThree (hΛ .sigma),
    woodinCardinalNextPiCertificate_piThree (woodinCardinalNextCertificate_sigmaThree (hΛ .sigma)), ?_⟩
  intro V _ _ _ k s K
  dsimp only
  intro hR ht hk hex z
  have he (w : V) := eval_woodinCardinalNextCertificate Λ w k s K (fun δ ↦
    (heΛ V _ _ _ _ δ hR ht hk).trans (woodinPrefixCutoff_eq_iff_least_of_exists hex).symm)
  exact ⟨he z, eval_woodinCardinalNextPiCertificate _ z k s K he⟩

end ZFVP
