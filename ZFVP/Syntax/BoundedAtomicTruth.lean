import ZFVP.Syntax.DirectMembershipAtoms
import ZFVP.Syntax.BoundedConstructorExpressions

/-! Bounded evaluation of the atomic formulas of the membership language. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def boundedAtomicTruthFormula : SetTheorySemisentence 5 :=
  “U n b r args. ∃ i ∈ n, ∃ j ∈ n,
    !(CodeExpression.boundArgs (.var 0) (.var 1)).formula U args i j ∧
    ∃ x ∈ U, ∃ y ∈ U, !boundedPairMemberFormula b i x ∧ !boundedPairMemberFormula b j y ∧
      (((!boundedEmptyFormula r ∨ !(CodeExpression.relation (.num 0)).formula U r) ∧ x = y) ∨
        (!(CodeExpression.relation (.num 1)).formula U r ∧ x ∈ y))”

theorem boundedAtomicTruthFormula_bounded : IsBoundedSetFormula boundedAtomicTruthFormula :=
  .exs (.bvar 1) (.exs (.bvar 2) (.and ((CodeExpression.boundArgs (.var 0) (.var 1)).formula_bounded.subst _)
    (.exs (.bvar 2) (.exs (.bvar 3) (.and (boundedPairMemberFormula_bounded.subst _)
      (.and (boundedPairMemberFormula_bounded.subst _)
        (.or (.and (.or (boundedEmptyFormula_bounded.subst _)
          ((CodeExpression.relation (.num 0)).formula_bounded.subst _)) (.rel _ _))
          (.and ((CodeExpression.relation (.num 1)).formula_bounded.subst _) (.rel _ _)))))))))

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem eval_boundedAtomicTruthFormula {U n b : V} [hU : IsCodingSupport U]
    (hn : n ∈ U) (hb : b ∈ U ^ n) (r args : V) :
    boundedAtomicTruthFormula.Evalb ![U, n, b, r, args] ↔ DirectMembershipAtomicHolds n b r args := by
  have : IsFunction b := IsFunction.of_mem hb
  simp [boundedAtomicTruthFormula, Matrix.comp_vecCons', Function.comp_def, Matrix.constant_eq_singleton,
    CodeExpression.eval, DirectMembershipAtomicHolds, equalityToken]
  refine exists_congr fun i ↦ and_congr_right fun hi ↦ exists_congr fun j ↦ and_congr_right fun hj ↦ ?_
  rw [CodeExpression.eval_formula_two _ _ _ _ _ (hU.mem_trans hi hn) (hU.mem_trans hj hn)]
  simp [CodeExpression.eval, kpair_mem_iff_value, domain_eq_of_mem_function hb,
    hi, hj, function_value_mem hb hi, function_value_mem hb hj]

end ZFVP
