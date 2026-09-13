import ZFVP.ModelTheory.ForcingClosedModelName
import ZFVP.SetTheory.WoodinClosedZFModels
import ZFVP.Syntax.SigmaOneBoundedForcing

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

def closedModelForcingCertificateFormula (σ : SetTheorySemisentence 5) : SetTheorySemisentence 8 :=
  “U P R o p a Z d. d ∈ U ∧ !IsTransitive.dfn U ∧ !sigmaOneOpenModelFormula U Z ∧
    ∃ k, ∃ ν, !(sigmaOneCheckNameFormula true) o a k ∧
      !sigmaOneClosedModelNameFormula ν P o U ∧ !σ P R p k ν”

theorem closedModelForcingCertificateFormula_sigmaOne {σ : SetTheorySemisentence 5}
    (hσ : IsSigmaFormula 1 σ) : IsSigmaFormula 1 (closedModelForcingCertificateFormula σ) :=
  .and (.bounded (.rel _ _)) (.and (.bounded (isTransitiveFormula_bounded.subst _))
    (.and (sigmaOneOpenModelFormula_sigmaOne.subst _) (.exs (.exs
      (.and ((sigmaOneCheckNameFormula_sigmaOne true).subst _)
        (.and (sigmaOneClosedModelNameFormula_sigmaOne.subst _) (hσ.subst _)))))))

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem eval_closedModelForcingCertificateFormula (σ : SetTheorySemisentence 5)
    (U P R one p a Z d : V) :
    (closedModelForcingCertificateFormula σ).Evalb ![U, P, R, one, p, a, Z, d] ↔
      d ∈ U ∧ IsTransitive U ∧ SatisfiesOpenCodes U Z ∧
        σ.Evalb ![P, R, p, checkName one a, closedModelName P one U] := by
  simp [closedModelForcingCertificateFormula, eval_sigmaOneOpenModelFormula,
    eval_sigmaOneCheckNameFormula, eval_sigmaOneClosedModelNameFormula, TruthAnswer,
    Matrix.comp_vecCons', Function.comp_def, Matrix.constant_eq_singleton]

theorem IsSigmaOneStarCorrect.reflect_closedModel_forcing {δ γ θ P R one p a d : V}
    (hδ : IsWoodinSupercompact δ) (hγ : IsSigmaOneStarCorrect γ) (hθ : θ ∈ γ)
    (hP : P ∈ hierarchy γ) (hR : R ∈ hierarchy γ) (hone : one ∈ hierarchy γ)
    (hp : p ∈ hierarchy γ) (ha : a ∈ hierarchy γ) (hd : d ∈ hierarchy γ)
    (horder : IsForcingPreorder P R) (htop : IsForcingTop P R one)
    {φ : SetTheorySemisentence 2} (hφ : IsBoundedSetFormula φ)
    (hex : ∃ U : V, IsRankFunctionClosed θ U ∧ d ∈ U ∧ IsTransitive U ∧ IsInternalZFModel U ∧
      p ∈ forcingFormula P R φ (standardTuple ![checkName one a, closedModelName P one U])) :
    ∃ U ∈ hierarchy γ, IsRankFunctionClosed θ U ∧ d ∈ U ∧ IsTransitive U ∧ IsInternalZFModel U ∧
      p ∈ forcingFormula P R φ (standardTuple ![checkName one a, closedModelName P one U]) := by
  obtain ⟨σ, _, hσ, _, hmean⟩ := bounded_forcing_deltaOne_formulas (V := V) hφ
  have he (U : V) : σ.Evalb ![P, R, p, checkName one a, closedModelName P one U] ↔
      p ∈ forcingFormula P R φ (standardTuple ![checkName one a, closedModelName P one U]) := by
    exact (hmean P R horder (IsForcingName P) (by definability) (fun _ h ↦ h)
      (fun _ h _ _ hm ↦ forcingName_subname h hm) ![checkName one a, closedModelName P one U]
      (by simp [Fin.forall_fin_iff_zero_and_forall_succ, checkName_isName htop.1,
        closedModelName_isName htop.1]) p).1
  have hw : ∃ U : V, IsRankFunctionClosed θ U ∧
      (closedModelForcingCertificateFormula σ).Evalb ![U, P, R, one, p, a, zfOpenAxiomCodes, d] := by
    obtain ⟨U, hc, hdU, ht, hm, hf⟩ := hex
    exact ⟨U, hc, (eval_closedModelForcingCertificateFormula _ _ _ _ _ _ _ _ _).mpr
      ⟨hdU, ht, hm.satisfies_open_codes, (he U).mpr hf⟩⟩
  obtain ⟨U, hU, hc, ht⟩ := hγ.reflect_rankClosed_sigmaOne_parameters hδ hθ
    (closedModelForcingCertificateFormula_sigmaOne hσ) ![P, R, one, p, a, zfOpenAxiomCodes, d]
    (by simp [Fin.forall_fin_iff_zero_and_forall_succ, hP, hR, hone, hp, ha, hd,
      hγ.1.zfOpenAxiomCodes_mem]) hw
  obtain ⟨hdU, htrans, hm, hf⟩ := (eval_closedModelForcingCertificateFormula _ _ _ _ _ _ _ _ _).mp ht
  exact ⟨U, hU, hc, hdU, htrans, (satisfiesOpenCodes_zf_iff U).mp hm, (he U).mp hf⟩

end ZFVP
