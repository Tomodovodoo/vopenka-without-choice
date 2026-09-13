import ZFVP.Syntax.BoundedConstructorExpressions

/-! A bounded definition of atomic arguments, relative to a coding support. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def boundedAtomicArgumentsFormula : SetTheorySemisentence 4 :=
  “U n r args. (!boundedEmptyFormula r ∨
    !(CodeExpression.relation (.num 0)).formula U r ∨
    !(CodeExpression.relation (.num 1)).formula U r) ∧
    ∃ i ∈ n, ∃ j ∈ n, !(CodeExpression.boundArgs (.var 0) (.var 1)).formula U args i j”

theorem boundedAtomicArgumentsFormula_bounded : IsBoundedSetFormula boundedAtomicArgumentsFormula := by
  exact .and (.or (boundedEmptyFormula_bounded.subst _)
    (.or ((CodeExpression.relation (.num 0)).formula_bounded.subst _)
      ((CodeExpression.relation (.num 1)).formula_bounded.subst _)))
    (.exs (.bvar 1) (.exs (.bvar 2) ((CodeExpression.boundArgs (.var 0) (.var 1)).formula_bounded.subst _)))

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem eval_boundedAtomicArgumentsFormula {U : V} [hU : IsCodingSupport U]
    {n : V} (hn : n ∈ U) (r args : V) :
    boundedAtomicArgumentsFormula.Evalb ![U, n, r, args] ↔ IsMembershipAtomicArguments n r args := by
  have he (i : V) (hi : i ∈ n) (j : V) (hj : j ∈ n) :
      (CodeExpression.boundArgs (.var 0) (.var 1)).formula.Evalb ![U, args, i, j] ↔
        args = boundPairArguments i j := by
    rw [CodeExpression.eval_formula_two _ _ _ _ _ (hU.mem_trans hi hn) (hU.mem_trans hj hn)]
    simp [CodeExpression.eval]
  simp [boundedAtomicArgumentsFormula, CodeExpression.eval, IsMembershipAtomicArguments, equalityToken]
  intro _
  constructor
  · rintro ⟨i, hi, j, hj, h⟩
    exact ⟨i, hi, j, hj, (he i hi j hj).mp h⟩
  · rintro ⟨i, hi, j, hj, h⟩
    exact ⟨i, hi, j, hj, (he i hi j hj).mpr h⟩

end ZFVP
