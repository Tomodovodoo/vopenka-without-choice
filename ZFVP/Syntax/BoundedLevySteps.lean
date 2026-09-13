import ZFVP.Syntax.LevyDerivationSteps

/-! Bounded formulas for the constructor rules of a Levy extension. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def levyQuantifierExpression (p : LevyPolarity) : CodeExpression 1 :=
  match p with
  | .sigma => CodeExpression.exs (.var 0)
  | .pi => CodeExpression.all (.var 0)

def boundedLevyQuantifierCaseFormula (p : LevyPolarity) : SetTheorySemisentence 5 :=
  “U s i n φ. ∃ ψ ∈ U, !boundedShiftedPreviousFormula U s i n ψ ∧
    !(levyQuantifierExpression p).formula U φ ψ”

def boundedLevyStepFormula (p : LevyPolarity) : SetTheorySemisentence 6 :=
  “U O B s i q. q ∈ B ∨ ∃ n ∈ O, ∃ φ ∈ U, !boundedKpairFormula q n φ ∧
    (!boundedBooleanCaseFormula U s i n φ ∨ !boundedQuantifierCaseFormula U s i n φ ∨
      !(boundedLevyQuantifierCaseFormula p) U s i n φ)”

theorem boundedLevyQuantifierCaseFormula_bounded (p : LevyPolarity) :
    IsBoundedSetFormula (boundedLevyQuantifierCaseFormula p) :=
  .exs (.bvar 0) (.and (boundedShiftedPreviousFormula_bounded.subst _)
    ((levyQuantifierExpression p).formula_bounded.subst _))

theorem boundedLevyStepFormula_bounded (p : LevyPolarity) : IsBoundedSetFormula (boundedLevyStepFormula p) :=
  .or (.rel _ _) (.exs (.bvar 1) (.exs (.bvar 1) (.and (boundedKpairFormula_bounded.subst _)
    (.or (boundedBooleanCaseFormula_bounded.subst _) (.or (boundedQuantifierCaseFormula_bounded.subst _)
      ((boundedLevyQuantifierCaseFormula_bounded p).subst _))))))

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

@[simp] theorem eval_levyQuantifierExpression (p : LevyPolarity) (φ : V) :
    (levyQuantifierExpression p).eval ![φ] = levyQuantifierCode p φ := by cases p <;> rfl

theorem eval_boundedLevyQuantifierCaseFormula (p : LevyPolarity) {U n s : V} [IsCodingSupport U]
    (hn : n ∈ U) (hs : s ∈ U) (i φ : V) :
    (boundedLevyQuantifierCaseFormula p).Evalb ![U, s, i, n, φ] ↔
      ∃ ψ, ⟨succ n, ψ⟩ₖ ∈ range (s ↾ i) ∧ φ = levyQuantifierCode p ψ := by
  have he : (boundedLevyQuantifierCaseFormula p).Evalb ![U, s, i, n, φ] ↔
      ∃ ψ ∈ U, ⟨succ n, ψ⟩ₖ ∈ range (s ↾ i) ∧ φ = levyQuantifierCode p ψ := by
    simp [boundedLevyQuantifierCaseFormula, Matrix.comp_vecCons', Function.comp_def, Matrix.constant_eq_singleton]
    refine exists_congr fun ψ ↦ and_congr_right fun hψ ↦ ?_
    rw [eval_boundedShiftedPreviousFormula hn hψ, CodeExpression.eval_formula_one _ _ _ _ hψ,
      eval_levyQuantifierExpression]
  rw [he]
  constructor
  · rintro ⟨ψ, _, hψ, h⟩
    exact ⟨ψ, hψ, h⟩
  · rintro ⟨ψ, hψ, h⟩
    exact ⟨ψ, (previousCode_components_mem hs hψ).2, hψ, h⟩

theorem eval_boundedLevyStepFormula (p : LevyPolarity) {U s q : V} [IsCodingSupport U]
    (hs : s ∈ U) (hq : q ∈ U) (B i : V) :
    (boundedLevyStepFormula p).Evalb ![U, ω, B, s, i, q] ↔ LevyDerivationStep p B (range (s ↾ i)) q := by
  simp [boundedLevyStepFormula, LevyDerivationStep, Matrix.comp_vecCons', Function.comp_def, Matrix.constant_eq_singleton]
  apply or_congr_right
  have he (n : V) (hn : n ∈ (ω : V)) (φ : V) :
      (boundedBooleanCaseFormula.Evalb ![U, s, i, n, φ] ∨
        boundedQuantifierCaseFormula.Evalb ![U, s, i, n, φ] ∨
        (boundedLevyQuantifierCaseFormula p).Evalb ![U, s, i, n, φ]) ↔
      ((∃ ψ χ, ⟨n, ψ⟩ₖ ∈ range (s ↾ i) ∧ ⟨n, χ⟩ₖ ∈ range (s ↾ i) ∧ (φ = andCode ψ χ ∨ φ = orCode ψ χ)) ∨
        (∃ j ∈ n, ∃ ψ, ⟨succ n, ψ⟩ₖ ∈ range (s ↾ i) ∧ (φ = boundedAllCode j ψ ∨ φ = boundedExistsCode j ψ)) ∨
        ∃ ψ, ⟨succ n, ψ⟩ₖ ∈ range (s ↾ i) ∧ φ = levyQuantifierCode p ψ) := by
    rw [boundedBooleanCase_iff (IsCodingSupport.natural_mem hn) hs,
      boundedQuantifierCase_iff (IsCodingSupport.natural_mem hn) hs,
      eval_boundedLevyQuantifierCaseFormula p (IsCodingSupport.natural_mem hn) hs]
  constructor
  · rintro ⟨n, hn, φ, _, hp, h⟩
    refine ⟨n, hn, φ, hp, ?_⟩
    simpa using (he n hn φ).mp h
  · rintro ⟨n, hn, φ, hp, h⟩
    refine ⟨n, hn, φ, (kpair_components_mem_transitive (hp ▸ hq)).2, hp, ?_⟩
    apply (he n hn φ).mpr
    simpa using h

end ZFVP
