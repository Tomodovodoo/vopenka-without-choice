import ZFVP.Syntax.MembershipFixedPoints

/-! A bounded formula checks one step of an internally finite syntax derivation. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def boundedMembershipStepFormula : SetTheorySemisentence 5 :=
  “U O s i q. ∃ n ∈ O, ∃ φ ∈ U, !boundedKpairFormula q n φ ∧
    (!(CodeExpression.truth).formula U φ ∨ !(CodeExpression.falsity).formula U φ ∨
      !boundedAtomicCaseFormula U n φ ∨ !boundedBooleanCaseFormula U s i n φ ∨
      (!(boundedLevyQuantifierCaseFormula .pi) U s i n φ ∨ !(boundedLevyQuantifierCaseFormula .sigma) U s i n φ))”

theorem boundedMembershipStepFormula_bounded : IsBoundedSetFormula boundedMembershipStepFormula :=
  .exs (.bvar 1) (.exs (.bvar 1) (.and (boundedKpairFormula_bounded.subst _)
    (.or (CodeExpression.truth.formula_bounded.subst _)
      (.or (CodeExpression.falsity.formula_bounded.subst _)
        (.or (boundedAtomicCaseFormula_bounded.subst _)
          (.or (boundedBooleanCaseFormula_bounded.subst _) (.or ((boundedLevyQuantifierCaseFormula_bounded .pi).subst _) ((boundedLevyQuantifierCaseFormula_bounded .sigma).subst _))))))))

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem eval_boundedMembershipStepFormula {U s q : V} [IsCodingSupport U]
    (hs : s ∈ U) (hq : q ∈ U) (i : V) :
    boundedMembershipStepFormula.Evalb ![U, ω, s, i, q] ↔ MembershipDerivationStep (range (s ↾ i)) q := by
  have he (n : V) (hn : n ∈ (ω : V)) (φ : V) (hφ : φ ∈ U) :
      (boundedAtomicCaseFormula.Evalb ![U, n, φ] ∨
        boundedBooleanCaseFormula.Evalb ![U, s, i, n, φ] ∨
        ((boundedLevyQuantifierCaseFormula .pi).Evalb ![U, s, i, n, φ] ∨ (boundedLevyQuantifierCaseFormula .sigma).Evalb ![U, s, i, n, φ])) ↔
      ((∃ r args, IsMembershipAtomicArguments n r args ∧ (φ = atomCode r args ∨ φ = negAtomCode r args)) ∨
        (∃ ψ χ, ⟨n, ψ⟩ₖ ∈ range (s ↾ i) ∧ ⟨n, χ⟩ₖ ∈ range (s ↾ i) ∧
          (φ = andCode ψ χ ∨ φ = orCode ψ χ)) ∨
        ∃ ψ, ⟨succ n, ψ⟩ₖ ∈ range (s ↾ i) ∧
          (φ = allCode ψ ∨ φ = existsCode ψ)) := by
    rw [boundedAtomicCase_iff (IsCodingSupport.natural_mem hn) hφ,
      boundedBooleanCase_iff (IsCodingSupport.natural_mem hn) hs,
      eval_boundedLevyQuantifierCaseFormula .pi (IsCodingSupport.natural_mem hn) hs,
      eval_boundedLevyQuantifierCaseFormula .sigma (IsCodingSupport.natural_mem hn) hs]
    simp only [levyQuantifierCode]
    simp only [and_or_left, exists_or]
  simp [boundedMembershipStepFormula, Matrix.comp_vecCons', Function.comp_def, Matrix.constant_eq_singleton,
    MembershipDerivationStep]
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
