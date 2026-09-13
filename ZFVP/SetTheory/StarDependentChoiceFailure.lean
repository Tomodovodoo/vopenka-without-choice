import ZFVP.SetTheory.DependentChoiceFailureCertificate

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

def starDCFailureCertificateFormula : SetTheorySemisentence 2 :=
  “a B. !IsTransitive.dfn B ∧ !functionRestrictionClosedFormula B ∧
    ∃ κ ∈ B, ∃ D ∈ B, !boundedKpairFormula a κ D ∧ !boundedDependentChoiceFailureFormula κ B”

theorem starDCFailureCertificateFormula_bounded : IsBoundedSetFormula starDCFailureCertificateFormula :=
  .and (isTransitiveFormula_bounded.subst _) (.and (functionRestrictionClosedFormula_bounded.subst _)
    (.exs (.bvar 1) (.exs (.bvar 2) (.and (boundedKpairFormula_bounded.subst _)
      (boundedDependentChoiceFailureFormula_bounded.subst _)))))

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem eval_starDCFailureCertificateFormula (κ D B : V) :
    starDCFailureCertificateFormula.Evalb ![⟨κ, D⟩ₖ, B] ↔
      IsTransitive B ∧ IsFunctionRestrictionClosed B ∧ κ ∈ B ∧ D ∈ B ∧
        IsBoundedDependentChoiceFailure κ B := by
  simp [starDCFailureCertificateFormula]

theorem IsSigmaOneStarCorrect.dependentChoice_failure_witness_at {δ γ κ α : V}
    (hδ : IsWoodinSupercompact δ) (hγ : IsSigmaOneStarCorrect γ) (hα : α ∈ γ) (hκ : κ ∈ α)
    (hfail : ¬InternalDependentChoiceAt κ) :
    ∃ B ∈ hierarchy γ, IsRankFunctionClosed α B ∧ hierarchy α ∈ B ∧ κ ∈ B ∧
      IsTransitive B ∧ IsFunctionRestrictionClosed B ∧ IsBoundedDependentChoiceFailure κ B := by
  let := hγ.1.ordinal
  let := IsOrdinal.of_mem hα
  let := IsOrdinal.of_mem hκ
  have hκV : κ ∈ hierarchy γ := ordinal_mem_hierarchy_iff.mpr (IsOrdinal.toIsTransitive.mem_trans hκ hα)
  have hDV : hierarchy α ∈ hierarchy γ :=
    hγ.1.hierarchy_closed inferInstance (ordinal_mem_hierarchy_iff.mpr hα)
  have ha := kpair_mem_hierarchy_limit hγ.1.successor_closed hκV hDV
  have hex : ∃ B, IsRankFunctionClosed α B ∧
      starDCFailureCertificateFormula.Evalb ![⟨κ, hierarchy α⟩ₖ, B] := by
    obtain ⟨B, hc, hD, hk, ht, hr, hf⟩ := hδ.dependentChoice_failure_certificate_at hκ hfail
    exact ⟨B, hc, (eval_starDCFailureCertificateFormula _ _ _).mpr ⟨ht, hr, hk, hD, hf⟩⟩
  obtain ⟨B, hB, hc, hf⟩ := hγ.reflect hα ha starDCFailureCertificateFormula_bounded hex
  obtain ⟨ht, hr, hk, hD, hfail⟩ := (eval_starDCFailureCertificateFormula _ _ _).mp hf
  exact ⟨B, hB, hc, hD, hk, ht, hr, hfail⟩

theorem IsSigmaOneStarCorrect.dependentChoice_failure_witness {δ γ κ : V}
    (hδ : IsWoodinSupercompact δ) (hγ : IsSigmaOneStarCorrect γ) (hκ : κ ∈ γ)
    (hfail : ¬InternalDependentChoiceAt κ) :
    ∃ B ∈ hierarchy γ, IsRankFunctionClosed (succ κ) B ∧ hierarchy (succ κ) ∈ B ∧ κ ∈ B ∧
      IsTransitive B ∧ IsFunctionRestrictionClosed B ∧ IsBoundedDependentChoiceFailure κ B :=
  hγ.dependentChoice_failure_witness_at hδ (hγ.1.successor_closed κ hκ) (mem_succ_self κ) hfail

end ZFVP
