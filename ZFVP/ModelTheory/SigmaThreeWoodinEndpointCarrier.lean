import ZFVP.ModelTheory.SigmaThreeWoodinEndpointRecursion
import ZFVP.ModelTheory.WoodinEndpointLocalAbsoluteness
import ZFVP.ModelTheory.DeltaOneWoodinSourceCode

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

def endpointStageCarrierCertificate (Λ : SetTheorySemisentence 2) : SetTheorySemisentence 1 :=
  “z. ∃ i, !IsOrdinal.dfn i ∧ ∃ r, !Λ r i ∧ ∃ C, !sigmaOnePairFirstFormula C r ∧
    ∃ P, !sigmaOneForcingCodePFormula P C ∧ ∃ Q, !boundedValueFormula Q P i ∧
    ∃ p ∈ Q, !boundedKpairFormula z i p”

theorem endpointStageCarrierCertificate_sigmaThree {Λ : SetTheorySemisentence 2}
    (hΛ : IsSigmaFormula 3 Λ) : IsSigmaFormula 3 (endpointStageCarrierCertificate Λ) :=
  .exs (.and (.bounded (isOrdinalFormula_bounded.subst _))
    (.exs (.and (hΛ.subst _)
      (.exs (.and ((sigmaOnePairFirstFormula_sigmaOne.mono (by omega)).subst _)
        (.exs (.and ((sigmaOneForcingCodePFormula_sigmaOne.mono (by omega)).subst _)
          (.exs (.and (.bounded (boundedValueFormula_bounded.subst _))
            (.boundedExs (.bvar 0) (.bounded (boundedKpairFormula_bounded.subst _))))))))))))

def sigmaThreeEndpointStageCarrierFormula : SetTheorySemisentence 1 :=
  endpointStageCarrierCertificate sigmaThreeEndpointRecursionFormula

theorem sigmaThreeEndpointStageCarrierFormula_sigmaThree :
    IsSigmaFormula 3 sigmaThreeEndpointStageCarrierFormula :=
  endpointStageCarrierCertificate_sigmaThree sigmaThreeEndpointRecursionFormula_sigmaThree

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem eval_endpointStageCarrierCertificate (Λ : SetTheorySemisentence 2) (z : V)
    (he : ∀ i : V, IsOrdinal i → ∀ r : V, Λ.Evalb ![r, i] ↔ r = woodinIterationRec i) :
    (endpointStageCarrierCertificate Λ).Evalb ![z] ↔ IsWoodinLocalStageCondition z := by
  have hh : (endpointStageCarrierCertificate Λ).Evalb ![z] ↔
      ∃ i : V, IsOrdinal i ∧ ∃ r : V, Λ.Evalb ![r, i] ∧
        ∃ p ∈ (forcingCodeP (kpair.π₁ r)) ‘ i, z = ⟨i, p⟩ₖ := by
    simp [endpointStageCarrierCertificate, Semiformula.Evalb, Semiformula.eval_substs,
      Matrix.comp_vecCons', Matrix.constant_eq_singleton, Function.comp_def]
  rw [hh]
  constructor
  · rintro ⟨i, hi, r, hr, p, hp, hz⟩
    have heq := (he i hi r).mp hr
    exact ⟨i, p, hi, heq ▸ hp, hz⟩
  · rintro ⟨i, p, hi, hp, hz⟩
    exact ⟨i, hi, woodinIterationRec i, (he i hi _).mpr rfl, p, hp, hz⟩

/-- A fixed Sigma-three formula, evaluated inside the endpoint rank, defines
the actual stage-code carrier of the direct limit. -/
theorem eval_sigmaThreeEndpointStageCarrierFormula {δ : V}
    (hδ : IsWoodinSupercompact δ) (hAC : ¬InternalChoice V) :
    letI := hδ.inaccessible.1
    letI := rankDomain_nonempty hδ.inaccessible.2.1
    letI := hδ.inaccessible.rankCriterion.models_zf
    ∀ z : SetDomain (hierarchy δ), sigmaThreeEndpointStageCarrierFormula.Evalb ![z] ↔
      z.val ∈ woodinStageCarrier δ := by
  let := hδ.inaccessible.1
  let := rankDomain_nonempty hδ.inaccessible.2.1
  let := hδ.inaccessible.rankCriterion.models_zf
  intro z
  have he := eval_endpointStageCarrierCertificate sigmaThreeEndpointRecursionFormula z
    (eval_sigmaThreeEndpointRecursionFormula hδ hAC)
  exact he.trans ((Defined.eval_iff ![z]).symm.trans
    (eval_woodinLocalStageConditionFormula_endpoint hδ hAC z))

end ZFVP
