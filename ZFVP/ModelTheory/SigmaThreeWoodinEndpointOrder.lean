import ZFVP.ModelTheory.SigmaThreeWoodinEndpointCarrier

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

def sigmaOneCodeStageComparisonFormula : SetTheorySemisentence 6 :=
  “C i j k p q. ∃ E, !sigmaOneForcingCodeEFormula E C ∧
    ∃ R, !sigmaOneForcingCodeRFormula R C ∧
    ∃ ik, !boundedKpairFormula ik i k ∧ ∃ jk, !boundedKpairFormula jk j k ∧
    ∃ e, !boundedValueFormula e E ik ∧ ∃ f, !boundedValueFormula f E jk ∧
    ∃ a, !boundedValueFormula a e p ∧ ∃ b, !boundedValueFormula b f q ∧
    ∃ T, !boundedValueFormula T R k ∧ ∃ v, !boundedKpairFormula v a b ∧ v ∈ T”

theorem sigmaOneCodeStageComparisonFormula_sigmaOne :
    IsSigmaFormula 1 sigmaOneCodeStageComparisonFormula :=
  .exs (.and (sigmaOneForcingCodeEFormula_sigmaOne.subst _) (.exs (.and (sigmaOneForcingCodeRFormula_sigmaOne.subst _) (.exs (.and (.bounded (boundedKpairFormula_bounded.subst _)) (.exs (.and (.bounded (boundedKpairFormula_bounded.subst _)) (.exs (.and (.bounded (boundedValueFormula_bounded.subst _)) (.exs (.and (.bounded (boundedValueFormula_bounded.subst _)) (.exs (.and (.bounded (boundedValueFormula_bounded.subst _)) (.exs (.and (.bounded (boundedValueFormula_bounded.subst _)) (.exs (.and (.bounded (boundedValueFormula_bounded.subst _)) (.exs (.and (.bounded (boundedKpairFormula_bounded.subst _)) (.bounded (.rel _ _)))))))))))))))))))))

def endpointStageComparisonCertificate (Λ : SetTheorySemisentence 2) : SetTheorySemisentence 5 :=
  “i j k p q. !IsOrdinal.dfn k ∧ ∃ r, !Λ r k ∧
    ∃ C, !sigmaOnePairFirstFormula C r ∧ !sigmaOneCodeStageComparisonFormula C i j k p q”

theorem endpointStageComparisonCertificate_sigmaThree {Λ : SetTheorySemisentence 2}
    (hΛ : IsSigmaFormula 3 Λ) : IsSigmaFormula 3 (endpointStageComparisonCertificate Λ) :=
  .and (.bounded (isOrdinalFormula_bounded.subst _))
    (.exs (.and (hΛ.subst _) (.exs (.and ((sigmaOnePairFirstFormula_sigmaOne.mono (by omega)).subst _)
      ((sigmaOneCodeStageComparisonFormula_sigmaOne.mono (by omega)).subst _)))))

def endpointStageOrderCertificate (Λ : SetTheorySemisentence 2) : SetTheorySemisentence 2 :=
  “z w. !(endpointStageCarrierCertificate Λ) z ∧ !(endpointStageCarrierCertificate Λ) w ∧
    ∃ i, !sigmaOnePairFirstFormula i z ∧ ∃ j, !sigmaOnePairFirstFormula j w ∧
    ∃ p, !sigmaOnePairSecondFormula p z ∧ ∃ q, !sigmaOnePairSecondFormula q w ∧
    ((!isSubsetOf i j ∧ !(endpointStageComparisonCertificate Λ) i j j p q) ∨
      (!isSubsetOf j i ∧ !(endpointStageComparisonCertificate Λ) i j i p q))”

theorem endpointStageOrderCertificate_sigmaThree {Λ : SetTheorySemisentence 2}
    (hΛ : IsSigmaFormula 3 Λ) : IsSigmaFormula 3 (endpointStageOrderCertificate Λ) :=
  .and ((endpointStageCarrierCertificate_sigmaThree hΛ).subst _)
    (.and ((endpointStageCarrierCertificate_sigmaThree hΛ).subst _)
      (.exs (.and ((sigmaOnePairFirstFormula_sigmaOne.mono (by omega)).subst _)
        (.exs (.and ((sigmaOnePairFirstFormula_sigmaOne.mono (by omega)).subst _)
          (.exs (.and ((sigmaOnePairSecondFormula_sigmaOne.mono (by omega)).subst _)
            (.exs (.and ((sigmaOnePairSecondFormula_sigmaOne.mono (by omega)).subst _)
              (.or (.and (.bounded (isSubsetOf_bounded.subst _))
                ((endpointStageComparisonCertificate_sigmaThree hΛ).subst _))
                (.and (.bounded (isSubsetOf_bounded.subst _))
                  ((endpointStageComparisonCertificate_sigmaThree hΛ).subst _))))))))))))

def sigmaThreeEndpointStageOrderFormula : SetTheorySemisentence 2 :=
  endpointStageOrderCertificate sigmaThreeEndpointRecursionFormula

theorem sigmaThreeEndpointStageOrderFormula_sigmaThree :
    IsSigmaFormula 3 sigmaThreeEndpointStageOrderFormula :=
  endpointStageOrderCertificate_sigmaThree sigmaThreeEndpointRecursionFormula_sigmaThree

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

instance sigmaOneCodeStageComparisonFormula_defined :
    Defined (fun v : Fin 6 → V ↦
      ⟨((forcingCodeE (v 0)) ‘ ⟨v 1, v 3⟩ₖ) ‘ (v 4),
        ((forcingCodeE (v 0)) ‘ ⟨v 2, v 3⟩ₖ) ‘ (v 5)⟩ₖ ∈ (forcingCodeR (v 0)) ‘ (v 3))
      sigmaOneCodeStageComparisonFormula :=
  ⟨fun _ ↦ by simp [sigmaOneCodeStageComparisonFormula]⟩

theorem eval_endpointStageComparisonCertificate (Λ : SetTheorySemisentence 2) (i j k p q : V)
    (hk : IsOrdinal k) (he : ∀ r : V, Λ.Evalb ![r, k] ↔ r = woodinIterationRec k) :
    (endpointStageComparisonCertificate Λ).Evalb ![i, j, k, p, q] ↔ WoodinLocalComparison i j k p q := by
  simp only [Semiformula.Evalb] at he
  simp [endpointStageComparisonCertificate, Semiformula.eval_substs, Matrix.comp_vecCons',
    Matrix.constant_eq_singleton, Function.comp_def, he, hk, WoodinLocalComparison]

theorem eval_endpointStageOrderCertificate (Λ : SetTheorySemisentence 2) (z w : V)
    (he : ∀ i : V, IsOrdinal i → ∀ r : V, Λ.Evalb ![r, i] ↔ r = woodinIterationRec i) :
    (endpointStageOrderCertificate Λ).Evalb ![z, w] ↔
      IsWoodinLocalStageCondition z ∧ IsWoodinLocalStageCondition w ∧ WoodinLocalStageOrder z w := by
  have hr : (endpointStageOrderCertificate Λ).Evalb ![z, w] ↔
      (endpointStageCarrierCertificate Λ).Evalb ![z] ∧
      (endpointStageCarrierCertificate Λ).Evalb ![w] ∧
      ((kpair.π₁ z ⊆ kpair.π₁ w ∧ (endpointStageComparisonCertificate Λ).Evalb
        ![kpair.π₁ z, kpair.π₁ w, kpair.π₁ w, kpair.π₂ z, kpair.π₂ w]) ∨
       (kpair.π₁ w ⊆ kpair.π₁ z ∧ (endpointStageComparisonCertificate Λ).Evalb
        ![kpair.π₁ z, kpair.π₁ w, kpair.π₁ z, kpair.π₂ z, kpair.π₂ w])) := by
    simp [endpointStageOrderCertificate, Semiformula.Evalb, Semiformula.eval_substs,
      Matrix.comp_vecCons', Matrix.constant_eq_singleton, Function.comp_def]
  rw [hr, eval_endpointStageCarrierCertificate Λ z he, eval_endpointStageCarrierCertificate Λ w he]
  have hc (hz : IsWoodinLocalStageCondition z) (hw : IsWoodinLocalStageCondition w) :
      ((kpair.π₁ z ⊆ kpair.π₁ w ∧ (endpointStageComparisonCertificate Λ).Evalb
        ![kpair.π₁ z, kpair.π₁ w, kpair.π₁ w, kpair.π₂ z, kpair.π₂ w]) ∨
       (kpair.π₁ w ⊆ kpair.π₁ z ∧ (endpointStageComparisonCertificate Λ).Evalb
        ![kpair.π₁ z, kpair.π₁ w, kpair.π₁ z, kpair.π₂ z, kpair.π₂ w])) ↔ WoodinLocalStageOrder z w :=
    or_congr (and_congr Iff.rfl (eval_endpointStageComparisonCertificate Λ _ _ _ _ _
      hw.index_ordinal (he _ hw.index_ordinal)))
      (and_congr Iff.rfl (eval_endpointStageComparisonCertificate Λ _ _ _ _ _
        hz.index_ordinal (he _ hz.index_ordinal)))
  exact ⟨fun ⟨hz, hw, h⟩ ↦ ⟨hz, hw, (hc hz hw).mp h⟩,
    fun ⟨hz, hw, h⟩ ↦ ⟨hz, hw, (hc hz hw).mpr h⟩⟩

/-- The fixed Sigma-three order formula has the actual endpoint order as its
extension when interpreted inside the endpoint rank. -/
theorem eval_sigmaThreeEndpointStageOrderFormula {δ : V}
    (hδ : IsWoodinSupercompact δ) (hAC : ¬InternalChoice V) :
    letI := hδ.inaccessible.1
    letI := rankDomain_nonempty hδ.inaccessible.2.1
    letI := hδ.inaccessible.rankCriterion.models_zf
    ∀ z w : SetDomain (hierarchy δ), sigmaThreeEndpointStageOrderFormula.Evalb ![z, w] ↔
      ⟨z.val, w.val⟩ₖ ∈ woodinLocalOrderOn (woodinStageCarrier δ) := by
  let := hδ.inaccessible.1
  let := rankDomain_nonempty hδ.inaccessible.2.1
  let := hδ.inaccessible.rankCriterion.models_zf
  intro z w
  have he := eval_endpointStageOrderCertificate sigmaThreeEndpointRecursionFormula z w
    (eval_sigmaThreeEndpointRecursionFormula hδ hAC)
  apply he.trans
  apply Iff.trans ?_ (eval_woodinLocalStageOrderFormula_endpoint hδ hAC z w)
  exact and_congr (woodinLocalStageConditionFormula_defined.iff ![z]).symm
    (and_congr (woodinLocalStageConditionFormula_defined.iff ![w]).symm (woodinLocalStageOrderFormula_defined.iff ![z, w]).symm)

end ZFVP
