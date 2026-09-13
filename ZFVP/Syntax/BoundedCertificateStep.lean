import ZFVP.Syntax.BoundedCertificateCases

/-! A bounded formula checks one step of an internally finite syntax derivation. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def boundedCertificateStepFormula : SetTheorySemisentence 5 :=
  “U O s i q. ∃ n ∈ O, ∃ φ ∈ U, !boundedKpairFormula q n φ ∧
    (!(CodeExpression.truth).formula U φ ∨ !(CodeExpression.falsity).formula U φ ∨
      !boundedAtomicCaseFormula U n φ ∨ !boundedBooleanCaseFormula U s i n φ ∨
      !boundedQuantifierCaseFormula U s i n φ)”

theorem boundedCertificateStepFormula_bounded : IsBoundedSetFormula boundedCertificateStepFormula :=
  .exs (.bvar 1) (.exs (.bvar 1) (.and (boundedKpairFormula_bounded.subst _)
    (.or (CodeExpression.truth.formula_bounded.subst _)
      (.or (CodeExpression.falsity.formula_bounded.subst _)
        (.or (boundedAtomicCaseFormula_bounded.subst _)
          (.or (boundedBooleanCaseFormula_bounded.subst _) (boundedQuantifierCaseFormula_bounded.subst _)))))))

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem eval_boundedCertificateStepFormula {U s q : V} [IsCodingSupport U]
    (hs : s ∈ U) (hq : q ∈ U) (i : V) :
    boundedCertificateStepFormula.Evalb ![U, ω, s, i, q] ↔ BoundedDerivationStep (range (s ↾ i)) q := by
  have he (n : V) (hn : n ∈ (ω : V)) (φ : V) (hφ : φ ∈ U) :
      (boundedAtomicCaseFormula.Evalb ![U, n, φ] ∨
        boundedBooleanCaseFormula.Evalb ![U, s, i, n, φ] ∨
        boundedQuantifierCaseFormula.Evalb ![U, s, i, n, φ]) ↔
      ((∃ r args, IsMembershipAtomicArguments n r args ∧ (φ = atomCode r args ∨ φ = negAtomCode r args)) ∨
        (∃ ψ χ, ⟨n, ψ⟩ₖ ∈ range (s ↾ i) ∧ ⟨n, χ⟩ₖ ∈ range (s ↾ i) ∧
          (φ = andCode ψ χ ∨ φ = orCode ψ χ)) ∨
        ∃ j ∈ n, ∃ ψ, ⟨succ n, ψ⟩ₖ ∈ range (s ↾ i) ∧
          (φ = boundedAllCode j ψ ∨ φ = boundedExistsCode j ψ)) := by
    rw [boundedAtomicCase_iff (IsCodingSupport.natural_mem hn) hφ,
      boundedBooleanCase_iff (IsCodingSupport.natural_mem hn) hs,
      boundedQuantifierCase_iff (IsCodingSupport.natural_mem hn) hs]
  simp [boundedCertificateStepFormula, Matrix.comp_vecCons', Function.comp_def, Matrix.constant_eq_singleton,
    BoundedDerivationStep]
  constructor
  · rintro ⟨n, hn, φ, hφ, hp, h⟩
    refine ⟨n, hn, φ, hp, ?_⟩
    simpa using (or_congr Iff.rfl (or_congr Iff.rfl (he n hn φ hφ))).mp h
  · rintro ⟨n, hn, φ, hp, h⟩
    have hφ := (kpair_components_mem_transitive (hp ▸ hq)).2
    refine ⟨n, hn, φ, hφ, hp, ?_⟩
    apply (or_congr Iff.rfl (or_congr Iff.rfl (he n hn φ hφ))).mpr
    simpa using h

end ZFVP
