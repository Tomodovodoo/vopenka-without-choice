import ZFVP.Syntax.InternalForcingSatisfaction
import ZFVP.Syntax.BoundedAtomicTruth
import ZFVP.SetTheory.BoundedAtomicMembership

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

def boundedInternalForcingAtomicFormula : SetTheorySemisentence 9 :=
  “U P R H n b r args p. ∃ i ∈ n, ∃ j ∈ n,
    !(CodeExpression.boundArgs (.var 0) (.var 1)).formula U args i j ∧
    ∃ x ∈ U, ∃ y ∈ U, !boundedPairMemberFormula b i x ∧ !boundedPairMemberFormula b j y ∧
      (((!boundedEmptyFormula r ∨ !(CodeExpression.relation (.num 0)).formula U r) ∧
        (p ∈ P ∧ !boundedTripleMemberFormula H x y p)) ∨
        (!(CodeExpression.relation (.num 1)).formula U r ∧ !boundedAtomicMembershipFormula U P R H x y p))”

theorem boundedInternalForcingAtomicFormula_bounded : IsBoundedSetFormula boundedInternalForcingAtomicFormula := by
  repeat' first
    | exact (CodeExpression.boundArgs (.var 0) (.var 1)).formula_bounded.subst _
    | exact (CodeExpression.relation (.num 0)).formula_bounded.subst _
    | exact (CodeExpression.relation (.num 1)).formula_bounded.subst _
    | exact boundedEmptyFormula_bounded.subst _
    | exact boundedPairMemberFormula_bounded.subst _
    | exact boundedTripleMemberFormula_bounded.subst _
    | exact boundedAtomicMembershipFormula_bounded.subst _
    | exact IsBoundedSetFormula.rel _ _
    | apply IsBoundedSetFormula.exs
    | apply IsBoundedSetFormula.and
    | apply IsBoundedSetFormula.or

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem eval_boundedInternalForcingAtomicFormula {U P R H n b : V} [hU : IsCodingSupport U]
    (hH : IsAtomicTruthTable P R U H) (hn : n ∈ U) (hb : b ∈ U ^ n) (r args p : V) :
    boundedInternalForcingAtomicFormula.Evalb ![U, P, R, H, n, b, r, args, p] ↔
      InternalForcingAtomicHolds P R n b r args p := by
  let := IsFunction.of_mem hb
  simp [boundedInternalForcingAtomicFormula, Matrix.comp_vecCons', Function.comp_def,
    Matrix.constant_eq_singleton, InternalForcingAtomicHolds, equalityToken]
  refine exists_congr fun i ↦ and_congr_right fun hi ↦ exists_congr fun j ↦ and_congr_right fun hj ↦ ?_
  rw [CodeExpression.eval_formula_two _ _ _ _ _ (hU.mem_trans hi hn) (hU.mem_trans hj hn)]
  simp [CodeExpression.eval, kpair_mem_iff_value, domain_eq_of_mem_function hb,
    hi, hj, function_value_mem hb hi, function_value_mem hb hj]
  rw [eval_boundedAtomicMembershipFormula hH (function_value_mem hb hi) (function_value_mem hb hj),
    hH.entry (transitive_subnameClosed hU.toIsTransitive) (function_value_mem hb hi) (function_value_mem hb hj)]
  exact fun _ ↦ Iff.rfl

end ZFVP
