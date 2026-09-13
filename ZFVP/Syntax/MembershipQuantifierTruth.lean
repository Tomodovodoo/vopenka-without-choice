import ZFVP.Syntax.BoundedQuantifierTruth
import ZFVP.Syntax.MembershipTruthTables

/-! Bounded truth-table clauses for quantifiers over a set domain. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def membershipAllTruthBodyFormula : SetTheorySemisentence 7 :=
  “U O T n b A φ. ∀ x ∈ A, !boundedTruthPrependLookupFormula U O T n b x φ”

def membershipExistsTruthBodyFormula : SetTheorySemisentence 7 :=
  “U O T n b A φ. ∃ x ∈ A, !boundedTruthPrependLookupFormula U O T n b x φ”

def membershipQuantifierTruthClause : SetTheorySemisentence 7 :=
  “U O T n b A φ.
    (!(CodeExpression.kpair (.var 0) (.all (.var 1))).lookupFormula U T b n φ ↔
      !membershipAllTruthBodyFormula U O T n b A φ) ∧
    (!(CodeExpression.kpair (.var 0) (.exs (.var 1))).lookupFormula U T b n φ ↔
      !membershipExistsTruthBodyFormula U O T n b A φ)”

theorem membershipAllTruthBodyFormula_bounded : IsBoundedSetFormula membershipAllTruthBodyFormula :=
  .all (.bvar 5) (boundedTruthPrependLookupFormula_bounded.subst _)

theorem membershipExistsTruthBodyFormula_bounded : IsBoundedSetFormula membershipExistsTruthBodyFormula :=
  .exs (.bvar 5) (boundedTruthPrependLookupFormula_bounded.subst _)

theorem membershipQuantifierTruthClause_bounded : IsBoundedSetFormula membershipQuantifierTruthClause :=
  .and (((CodeExpression.kpair (.var 0) (.all (.var 1))).lookupFormula_bounded.subst _).iff
    (membershipAllTruthBodyFormula_bounded.subst _))
    (((CodeExpression.kpair (.var 0) (.exs (.var 1))).lookupFormula_bounded.subst _).iff
      (membershipExistsTruthBodyFormula_bounded.subst _))

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem eval_membershipAllTruthBodyFormula {U A n b φ : V} [IsSequenceSupport U]
    (hA : A ⊆ U) (hn : n ∈ (ω : V)) (hb : b ∈ A ^ n) (hφ : φ ∈ U) (T : V) :
    membershipAllTruthBodyFormula.Evalb ![U, ω, T, n, b, A, φ] ↔
      ∀ x ∈ A, TableHolds T (succ n) φ (assignmentPrepend n b x) := by
  simp [membershipAllTruthBodyFormula, Matrix.comp_vecCons', Function.comp_def, Matrix.constant_eq_singleton]
  exact forall_congr' fun x ↦ imp_congr_right fun hx ↦ eval_boundedTruthPrependLookupFormula hA hn hb hx hφ T

theorem eval_membershipExistsTruthBodyFormula {U A n b φ : V} [IsSequenceSupport U]
    (hA : A ⊆ U) (hn : n ∈ (ω : V)) (hb : b ∈ A ^ n) (hφ : φ ∈ U) (T : V) :
    membershipExistsTruthBodyFormula.Evalb ![U, ω, T, n, b, A, φ] ↔
      ∃ x ∈ A, TableHolds T (succ n) φ (assignmentPrepend n b x) := by
  simp [membershipExistsTruthBodyFormula, Matrix.comp_vecCons', Function.comp_def, Matrix.constant_eq_singleton]
  exact exists_congr fun x ↦ and_congr_right fun hx ↦ eval_boundedTruthPrependLookupFormula hA hn hb hx hφ T

theorem eval_membershipQuantifierTruthClause {U A n b φ : V} [IsSequenceSupport U]
    (hA : A ⊆ U) (hn : n ∈ (ω : V)) (hb : b ∈ A ^ n) (hφ : φ ∈ U) (T : V) :
    membershipQuantifierTruthClause.Evalb ![U, ω, T, n, b, A, φ] ↔
      (TableHolds T n (allCode φ) b ↔ ∀ x ∈ A, TableHolds T (succ n) φ (assignmentPrepend n b x)) ∧
      (TableHolds T n (existsCode φ) b ↔ ∃ x ∈ A, TableHolds T (succ n) φ (assignmentPrepend n b x)) := by
  have hnU : n ∈ U := IsCodingSupport.natural_mem hn
  simp [membershipQuantifierTruthClause, Matrix.comp_vecCons', Function.comp_def, Matrix.constant_eq_singleton]
  rw [CodeExpression.eval_lookupFormula_two _ T b hnU hφ,
    CodeExpression.eval_lookupFormula_two _ T b hnU hφ,
    eval_membershipAllTruthBodyFormula hA hn hb hφ, eval_membershipExistsTruthBodyFormula hA hn hb hφ]
  simp [CodeExpression.eval, TableHolds]

end ZFVP
