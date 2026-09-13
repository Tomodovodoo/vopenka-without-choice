import ZFVP.Syntax.BoundedAtomicTruth
import ZFVP.Syntax.BoundedExpressionLookup
import ZFVP.Syntax.BoundedTruthTables

/-! Bounded formulas checking the constant, atomic and Boolean truth clauses. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

theorem IsBoundedSetFormula.iff {n : ℕ} {φ ψ : SetTheorySemisentence n}
    (hφ : IsBoundedSetFormula φ) (hψ : IsBoundedSetFormula ψ) : IsBoundedSetFormula (φ 🡘 ψ) :=
  .and (.or hφ.neg hψ) (.or hψ.neg hφ)

def boundedConstantTruthClause : SetTheorySemisentence 4 :=
  “U T n b. !(CodeExpression.kpair (.var 0) .truth).lookupFormula U T b n ∧
    ¬!(CodeExpression.kpair (.var 0) .falsity).lookupFormula U T b n”

def boundedAtomicTruthClause : SetTheorySemisentence 6 :=
  “U T n b r args.
    (!(CodeExpression.kpair (.var 0) (.atom (.var 1) (.var 2))).lookupFormula U T b n r args ↔
      !boundedAtomicTruthFormula U n b r args) ∧
    (!(CodeExpression.kpair (.var 0) (.negAtom (.var 1) (.var 2))).lookupFormula U T b n r args ↔
      ¬!boundedAtomicTruthFormula U n b r args)”

def boundedBooleanTruthClause : SetTheorySemisentence 6 :=
  “U T n b φ ψ.
    (!(CodeExpression.kpair (.var 0) (.conj (.var 1) (.var 2))).lookupFormula U T b n φ ψ ↔
      (!(CodeExpression.kpair (.var 0) (.var 1)).lookupFormula U T b n φ ∧
        !(CodeExpression.kpair (.var 0) (.var 1)).lookupFormula U T b n ψ)) ∧
    (!(CodeExpression.kpair (.var 0) (.disj (.var 1) (.var 2))).lookupFormula U T b n φ ψ ↔
      (!(CodeExpression.kpair (.var 0) (.var 1)).lookupFormula U T b n φ ∨
        !(CodeExpression.kpair (.var 0) (.var 1)).lookupFormula U T b n ψ))”

theorem boundedConstantTruthClause_bounded : IsBoundedSetFormula boundedConstantTruthClause :=
  .and ((CodeExpression.kpair (.var 0) .truth).lookupFormula_bounded.subst _)
    ((CodeExpression.kpair (.var 0) .falsity).lookupFormula_bounded.subst _).neg

theorem boundedAtomicTruthClause_bounded : IsBoundedSetFormula boundedAtomicTruthClause :=
  .and (((CodeExpression.kpair (.var 0) (.atom (.var 1) (.var 2))).lookupFormula_bounded.subst _).iff
    (boundedAtomicTruthFormula_bounded.subst _))
    (((CodeExpression.kpair (.var 0) (.negAtom (.var 1) (.var 2))).lookupFormula_bounded.subst _).iff
      (boundedAtomicTruthFormula_bounded.subst _).neg)

theorem boundedBooleanTruthClause_bounded : IsBoundedSetFormula boundedBooleanTruthClause :=
  .and (((CodeExpression.kpair (.var 0) (.conj (.var 1) (.var 2))).lookupFormula_bounded.subst _).iff
    (.and ((CodeExpression.kpair (.var 0) (.var 1)).lookupFormula_bounded.subst _)
      ((CodeExpression.kpair (.var 0) (.var 1)).lookupFormula_bounded.subst _)))
    (((CodeExpression.kpair (.var 0) (.disj (.var 1) (.var 2))).lookupFormula_bounded.subst _).iff
      (.or ((CodeExpression.kpair (.var 0) (.var 1)).lookupFormula_bounded.subst _)
        ((CodeExpression.kpair (.var 0) (.var 1)).lookupFormula_bounded.subst _)))

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem eval_boundedConstantTruthClause {U n : V} [IsCodingSupport U] (hn : n ∈ U) (T b : V) :
    boundedConstantTruthClause.Evalb ![U, T, n, b] ↔ TableHolds T n truthCode b ∧ ¬TableHolds T n falsityCode b := by
  simp [boundedConstantTruthClause, hn, CodeExpression.eval, TableHolds]

theorem eval_boundedAtomicTruthClause {U n b r args : V} [IsCodingSupport U]
    (hn : n ∈ U) (hb : b ∈ U ^ n) (hr : r ∈ U) (ha : args ∈ U) (T : V) :
    boundedAtomicTruthClause.Evalb ![U, T, n, b, r, args] ↔
      (TableHolds T n (atomCode r args) b ↔ DirectMembershipAtomicHolds n b r args) ∧
      (TableHolds T n (negAtomCode r args) b ↔ ¬DirectMembershipAtomicHolds n b r args) := by
  simp [boundedAtomicTruthClause, Matrix.comp_vecCons', Function.comp_def, Matrix.constant_eq_singleton]
  rw [CodeExpression.eval_lookupFormula_three _ T b hn hr ha,
    CodeExpression.eval_lookupFormula_three _ T b hn hr ha, eval_boundedAtomicTruthFormula hn hb]
  simp [CodeExpression.eval, TableHolds]

theorem eval_boundedBooleanTruthClause {U n φ ψ : V} [IsCodingSupport U]
    (hn : n ∈ U) (hφ : φ ∈ U) (hψ : ψ ∈ U) (T b : V) :
    boundedBooleanTruthClause.Evalb ![U, T, n, b, φ, ψ] ↔
      (TableHolds T n (andCode φ ψ) b ↔ TableHolds T n φ b ∧ TableHolds T n ψ b) ∧
      (TableHolds T n (orCode φ ψ) b ↔ TableHolds T n φ b ∨ TableHolds T n ψ b) := by
  simp [boundedBooleanTruthClause, Matrix.comp_vecCons', Function.comp_def, Matrix.constant_eq_singleton]
  rw [CodeExpression.eval_lookupFormula_three _ T b hn hφ hψ,
    CodeExpression.eval_lookupFormula_three _ T b hn hφ hψ,
    CodeExpression.eval_lookupFormula_two _ T b hn hφ, CodeExpression.eval_lookupFormula_two _ T b hn hψ]
  simp [CodeExpression.eval, TableHolds]

end ZFVP
