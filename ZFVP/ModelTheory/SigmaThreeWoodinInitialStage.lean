import ZFVP.ModelTheory.DeltaOneWoodinStageCode
import ZFVP.ModelTheory.SigmaThreeWoodinSuccessor
import ZFVP.SetTheory.DeltaThreeWoodinSeed

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
universe u

def woodinSuccessorAtCertificate (Ξ Ω : SetTheorySemisentence 6) (φ : BoundedFormulaTree 3) :
    SetTheorySemisentence 6 :=
  “z P R o κ δ. ∃ Q, !Ξ Q P R o κ δ ∧ ∃ S, !Ω S P R o κ δ ∧
    ∃ e, !boundedEmptyFormula e ∧ ∃ C, !sigmaOneTwoStepConditionSetFormula C P R Q e ∧
    ∃ T, !(sigmaOneTwoStepOrderSetFormula φ) T P R Q S e ∧
    ∃ u, !boundedKpairFormula u o e ∧ !sigmaOneWoodinStageCodeFormula z C T u δ”

theorem woodinSuccessorAtCertificate_sigmaThree {Ξ Ω : SetTheorySemisentence 6}
    (hΞ : IsSigmaFormula 3 Ξ) (hΩ : IsSigmaFormula 3 Ω) (φ : BoundedFormulaTree 3) :
    IsSigmaFormula 3 (woodinSuccessorAtCertificate Ξ Ω φ) :=
  .exs (.and (hΞ.subst _) (.exs (.and (hΩ.subst _)
    (.exs (.and (.bounded (boundedEmptyFormula_bounded.subst _))
      (.exs (.and ((sigmaOneTwoStepConditionSetFormula_sigmaOne.mono (by omega)).subst _)
        (.exs (.and (((sigmaOneTwoStepOrderSetFormula_sigmaOne φ).mono (by omega)).subst _)
          (.exs (.and (.bounded (boundedKpairFormula_bounded.subst _))
            ((sigmaOneWoodinStageCodeFormula_sigmaOne.mono (by omega)).subst _))))))))))))

def woodinInitialStageCertificate (Λ : SetTheorySemisentence 5) (Ξ : SetTheorySemisentence 6) :
    SetTheorySemisentence 1 :=
  “z. ∃ κ, !sigmaThreeWoodinSeedCardinalFormula κ ∧ ∃ o, !boundedEmptyFormula o ∧
    ∃ P, !boundedSingletonFormula P o ∧ ∃ R, !boundedProductFormula R P P ∧
    ∃ δ, !Λ P R o κ δ ∧ !Ξ z P R o κ δ”

theorem woodinInitialStageCertificate_sigmaThree {Λ : SetTheorySemisentence 5} {Ξ : SetTheorySemisentence 6}
    (hΛ : IsSigmaFormula 3 Λ) (hΞ : IsSigmaFormula 3 Ξ) : IsSigmaFormula 3 (woodinInitialStageCertificate Λ Ξ) :=
  .exs (.and (sigmaThreeWoodinSeedCardinalFormula_sigmaThree.subst _)
    (.exs (.and (.bounded (boundedEmptyFormula_bounded.subst _))
      (.exs (.and (.bounded (boundedSingletonFormula_bounded.subst _))
        (.exs (.and (.bounded (boundedProductFormula_bounded.subst _))
          (.exs (.and (hΛ.subst _) (hΞ.subst _))))))))))

def initialStagePiCertificate (Λ : SetTheorySemisentence 1) : SetTheorySemisentence 1 :=
  “z. ∀ w, !Λ w → z = w”

theorem initialStagePiCertificate_piThree {Λ : SetTheorySemisentence 1}
    (hΛ : IsSigmaFormula 3 Λ) : IsPiFormula 3 (initialStagePiCertificate Λ) :=
  .all (.or (hΛ.subst _).neg (.bounded (.rel _ _)))

variable {V : Type u} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem eval_woodinSuccessorAtCertificate (Ξ Ω : SetTheorySemisentence 6) (φ : BoundedFormulaTree 3)
    (hφ : φ.formula = boundedPairMemberFormula) (z P R o κ δ : V)
    (hΞ : ∀ Q : V, Ξ.Evalb ![Q, P, R, o, κ, δ] ↔ Q = saturatedWoodinPrefixPosetName P R o κ δ)
    (hΩ : ∀ S : V, Ω.Evalb ![S, P, R, o, κ, δ] ↔ S = saturatedWoodinPrefixOrderName P R o κ δ)
    (hR : IsForcingPreorder P R)
    (hI : IsForcingIterand P R (saturatedWoodinPrefixPosetName P R o κ δ)
      (saturatedWoodinPrefixOrderName P R o κ δ) ∅) :
    (woodinSuccessorAtCertificate Ξ Ω φ).Evalb ![z, P, R, o, κ, δ] ↔ z = woodinSuccessorAt P R o κ δ := by
  have he := eval_sigmaOneTwoStepOrderSetFormula φ hφ hR hI
  simp only [Semiformula.Evalb] at hΞ hΩ he
  simp [woodinSuccessorAtCertificate, Semiformula.eval_substs, Matrix.comp_vecCons',
    Matrix.constant_eq_singleton, Function.comp_def, hΞ, hΩ, he, woodinSuccessorAt]

theorem woodinSuccessorAt_sigmaThree_uniform :
    ∃ Λ : SetTheorySemisentence 6, IsSigmaFormula 3 Λ ∧
      ∀ (V : Type u) [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙], ∀ z P R o κ δ : V,
        IsForcingPreorder P R → IsForcingTop P R o →
        (∀ p ∈ P, p ∈ forcingFormula P R regularCardinalFormula (standardTuple ![checkName o κ])) →
        IsWoodinPrefixCutoff P R o κ δ → P ∈ hierarchy δ →
          (Λ.Evalb ![z, P, R, o, κ, δ] ↔ z = woodinSuccessorAt P R o κ δ) := by
  obtain ⟨Ξ, hΞ, heΞ⟩ := saturatedWoodinPrefixPosetName_sigmaThree_uniform.{u}
  obtain ⟨Ω, hΩ, heΩ⟩ := saturatedWoodinPrefixOrderName_sigmaThree_uniform.{u}
  obtain ⟨φ, hφ⟩ := boundedFormulaTree_exists boundedPairMemberFormula_bounded
  refine ⟨woodinSuccessorAtCertificate Ξ Ω φ, woodinSuccessorAtCertificate_sigmaThree hΞ hΩ φ, ?_⟩
  intro V _ _ _ z P R o κ δ hR ht hreg hδ hP
  exact eval_woodinSuccessorAtCertificate Ξ Ω φ hφ z P R o κ δ
    (fun Q ↦ heΞ V Q P R o κ δ hR ht hδ.2.1.1)
    (fun S ↦ heΩ V S P R o κ δ hR ht hδ.2.1.1) hR
    (saturatedWoodinPrefix_iterand_of_cutoff hR ht hreg hδ hP)

theorem eval_woodinInitialStageCertificate (Λ : SetTheorySemisentence 5) (Ξ : SetTheorySemisentence 6) (z : V)
    (hΛ : ∀ δ : V, Λ.Evalb ![{∅}, ({∅} : V) ×ˢ {∅}, ∅, woodinSeedCardinal, δ] ↔
      δ = woodinPrefixCutoff {∅} (({∅} : V) ×ˢ {∅}) ∅ woodinSeedCardinal)
    (hΞ : Ξ.Evalb ![z, {∅}, ({∅} : V) ×ˢ {∅}, ∅, woodinSeedCardinal,
      woodinPrefixCutoff {∅} (({∅} : V) ×ˢ {∅}) ∅ woodinSeedCardinal] ↔ z = woodinInitialStage) :
    (woodinInitialStageCertificate Λ Ξ).Evalb ![z] ↔ z = woodinInitialStage := by
  simp only [Semiformula.Evalb] at hΛ hΞ
  simp at hΛ hΞ
  simp [woodinInitialStageCertificate, Semiformula.eval_substs, Matrix.comp_vecCons',
    Matrix.constant_eq_singleton, Function.comp_def, hΛ, hΞ]

theorem eval_initialStagePiCertificate (Λ : SetTheorySemisentence 1) (z : V)
    (he : ∀ w : V, Λ.Evalb ![w] ↔ w = woodinInitialStage) :
    (initialStagePiCertificate Λ).Evalb ![z] ↔ z = woodinInitialStage := by
  simp only [Semiformula.Evalb] at he
  simp [initialStagePiCertificate, Semiformula.eval_substs, Matrix.comp_vecCons',
    Matrix.constant_eq_singleton, Function.comp_def, he]

theorem woodinInitialStage_sigmaThree_uniform :
    ∃ Λ : SetTheorySemisentence 1, IsSigmaFormula 3 Λ ∧
      ∀ (V : Type u) [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙],
        (∃ δ : V, IsWoodinSupercompact δ) → ∀ z : V, (Λ.Evalb ![z] ↔ z = woodinInitialStage) := by
  obtain ⟨Λ, hΛ, heΛ⟩ := leastWoodinPrefixCutoff_deltaThree_uniform.{u}
  obtain ⟨Ξ, hΞ, heΞ⟩ := woodinSuccessorAt_sigmaThree_uniform.{u}
  refine ⟨woodinInitialStageCertificate Λ Ξ, woodinInitialStageCertificate_sigmaThree (hΛ .sigma) hΞ, ?_⟩
  intro V _ _ _ hex z
  obtain ⟨δ, hδ⟩ := hex
  let := hδ.inaccessible.1
  have hx := woodinSeedStage_stage (V := V)
  have hs := woodinSeedStage_small (V := V)
  have hb : woodinStageCardinal (woodinSeedStage : V) ∈ δ := by
    simpa [woodinSeedStage] using woodinSeedCardinal_lt hδ
  have hP := hs δ hδ.inaccessible hb
  have hR := hx.order_mem_hierarchy hδ.inaccessible.rankCriterion.2.2.1 hP
  obtain ⟨c, _, hc⟩ := hδ.strictPrefixCutoff hx.1 hx.2.1 hP hR hb hx.2.2.2.1 hx.2.2.2.2
  have hl := (woodinPrefixCutoff_spec hc).2.1
  have hPl := hs _ hl.2.1 hl.1
  have hz : (∅ : V) ∈ woodinStageCardinal (woodinSeedStage : V) := by
    simpa [woodinSeedStage] using (woodinSeedCardinal_regular (V := V)).2.1 ∅ (by simp)
  apply eval_woodinInitialStageCertificate Λ Ξ z
  · intro d
    simpa [woodinSeedStage] using (heΛ V _ _ _ _ d hx.1 hx.2.1 hz).trans
      (woodinPrefixCutoff_eq_iff_least_of_exists ⟨c, hc⟩).symm
  · simpa [woodinInitialStage, woodinSuccessorStep, woodinSeedStage] using
      heΞ V z _ _ _ _ _ hx.1 hx.2.1 hx.2.2.2.1 hl hPl

theorem woodinInitialStage_deltaThree_uniform :
    ∃ Λ Ξ : SetTheorySemisentence 1, IsSigmaFormula 3 Λ ∧ IsPiFormula 3 Ξ ∧
      ∀ (V : Type u) [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙],
        (∃ δ : V, IsWoodinSupercompact δ) → ∀ z : V,
          (Λ.Evalb ![z] ↔ z = woodinInitialStage) ∧ (Ξ.Evalb ![z] ↔ z = woodinInitialStage) := by
  obtain ⟨Λ, hΛ, he⟩ := woodinInitialStage_sigmaThree_uniform.{u}
  refine ⟨Λ, initialStagePiCertificate Λ, hΛ, initialStagePiCertificate_piThree hΛ, ?_⟩
  intro V _ _ _ hδ z
  exact ⟨he V hδ z, eval_initialStagePiCertificate Λ z (he V hδ)⟩

end ZFVP
