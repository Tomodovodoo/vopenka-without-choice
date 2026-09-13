import ZFVP.Syntax.BoundedForcingLookup
import ZFVP.Syntax.BoundedInternalForcingAtoms
import ZFVP.Syntax.BoundedTruthClauses

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

def boundedForcingConstantClause : SetTheorySemisentence 5 :=
  “U T n b p. !(CodeExpression.kpair (.var 0) .truth).forcingLookupFormula U T b p n ∧
    ¬!(CodeExpression.kpair (.var 0) .falsity).forcingLookupFormula U T b p n”

def boundedForcingAtomicClause : SetTheorySemisentence 10 :=
  “U P R H T n b r args p.
    (!(CodeExpression.kpair (.var 0) (.atom (.var 1) (.var 2))).forcingLookupFormula U T b p n r args ↔
      !boundedInternalForcingAtomicFormula U P R H n b r args p) ∧
    (!(CodeExpression.kpair (.var 0) (.negAtom (.var 1) (.var 2))).forcingLookupFormula U T b p n r args ↔
      ∀ q ∈ P, !boundedPairMemberFormula R q p → ¬!boundedInternalForcingAtomicFormula U P R H n b r args q)”

def boundedForcingOrBody : SetTheorySemisentence 9 :=
  “U P R T n b p φ ψ. ∀ q ∈ P, !boundedPairMemberFormula R q p →
    ∃ r ∈ P, !boundedPairMemberFormula R r q ∧
      (!(CodeExpression.kpair (.var 0) (.var 1)).forcingLookupFormula U T b r n φ ∨
        !(CodeExpression.kpair (.var 0) (.var 1)).forcingLookupFormula U T b r n ψ)”

def boundedForcingBooleanClause : SetTheorySemisentence 9 :=
  “U P R T n b p φ ψ.
    (!(CodeExpression.kpair (.var 0) (.conj (.var 1) (.var 2))).forcingLookupFormula U T b p n φ ψ ↔
      (!(CodeExpression.kpair (.var 0) (.var 1)).forcingLookupFormula U T b p n φ ∧
        !(CodeExpression.kpair (.var 0) (.var 1)).forcingLookupFormula U T b p n ψ)) ∧
    (!(CodeExpression.kpair (.var 0) (.disj (.var 1) (.var 2))).forcingLookupFormula U T b p n φ ψ ↔
      !boundedForcingOrBody U P R T n b p φ ψ)”

theorem boundedForcingConstantClause_bounded : IsBoundedSetFormula boundedForcingConstantClause :=
  .and ((CodeExpression.kpair (.var 0) .truth).forcingLookupFormula_bounded.subst _)
    ((CodeExpression.kpair (.var 0) .falsity).forcingLookupFormula_bounded.subst _).neg

theorem boundedForcingAtomicClause_bounded : IsBoundedSetFormula boundedForcingAtomicClause :=
  .and (((CodeExpression.kpair (.var 0) (.atom (.var 1) (.var 2))).forcingLookupFormula_bounded.subst _).iff
    (boundedInternalForcingAtomicFormula_bounded.subst _))
    (((CodeExpression.kpair (.var 0) (.negAtom (.var 1) (.var 2))).forcingLookupFormula_bounded.subst _).iff
      (.all (.bvar 1) (.or (boundedPairMemberFormula_bounded.subst _).neg
        (boundedInternalForcingAtomicFormula_bounded.subst _).neg)))

theorem boundedForcingOrBody_bounded : IsBoundedSetFormula boundedForcingOrBody := by
  repeat' first
    | exact (CodeExpression.kpair (.var 0) (.var 1)).forcingLookupFormula_bounded.subst _
    | exact boundedPairMemberFormula_bounded.subst _
    | exact (boundedPairMemberFormula_bounded.subst _).neg
    | apply IsBoundedSetFormula.all
    | apply IsBoundedSetFormula.exs
    | apply IsBoundedSetFormula.and
    | apply IsBoundedSetFormula.or

theorem boundedForcingBooleanClause_bounded : IsBoundedSetFormula boundedForcingBooleanClause :=
  .and (((CodeExpression.kpair (.var 0) (.conj (.var 1) (.var 2))).forcingLookupFormula_bounded.subst _).iff
    (.and ((CodeExpression.kpair (.var 0) (.var 1)).forcingLookupFormula_bounded.subst _)
      ((CodeExpression.kpair (.var 0) (.var 1)).forcingLookupFormula_bounded.subst _)))
    (((CodeExpression.kpair (.var 0) (.disj (.var 1) (.var 2))).forcingLookupFormula_bounded.subst _).iff
      (boundedForcingOrBody_bounded.subst _))

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem eval_boundedForcingConstantClause {U n b p : V} [IsCodingSupport U]
    (hn : n ∈ U) (hb : b ∈ U) (hp : p ∈ U) (T : V) :
    boundedForcingConstantClause.Evalb ![U, T, n, b, p] ↔
      ForcingTableHolds T n truthCode b p ∧ ¬ForcingTableHolds T n falsityCode b p := by
  simp [boundedForcingConstantClause, Matrix.comp_vecCons', Function.comp_def, Matrix.constant_eq_singleton, hn, hb, hp, CodeExpression.eval, ForcingTableHolds]

theorem eval_boundedForcingAtomicClause {U P R H n b r args p : V} [IsCodingSupport U]
    (hH : IsAtomicTruthTable P R U H) (hn : n ∈ U) (hb : b ∈ U ^ n)
    (hbU : b ∈ U) (hp : p ∈ U) (hr : r ∈ U) (ha : args ∈ U) (T : V) :
    boundedForcingAtomicClause.Evalb ![U, P, R, H, T, n, b, r, args, p] ↔
      (ForcingTableHolds T n (atomCode r args) b p ↔ InternalForcingAtomicHolds P R n b r args p) ∧
      (ForcingTableHolds T n (negAtomCode r args) b p ↔
        ∀ q ∈ P, ⟨q, p⟩ₖ ∈ R → ¬InternalForcingAtomicHolds P R n b r args q) := by
  simp [boundedForcingAtomicClause, Matrix.comp_vecCons', Function.comp_def, Matrix.constant_eq_singleton]
  rw [CodeExpression.eval_forcingLookupFormula_three _ T hbU hp hn hr ha,
    CodeExpression.eval_forcingLookupFormula_three _ T hbU hp hn hr ha]
  simp only [eval_boundedInternalForcingAtomicFormula hH hn hb]
  simp [CodeExpression.eval, ForcingTableHolds]

theorem eval_boundedForcingOrBody {U P n b p φ ψ : V} [IsCodingSupport U]
    (hP : P ⊆ U) (hn : n ∈ U) (hb : b ∈ U) (hφ : φ ∈ U) (hψ : ψ ∈ U) (R T : V) :
    boundedForcingOrBody.Evalb ![U, P, R, T, n, b, p, φ, ψ] ↔
      ∀ q ∈ P, ⟨q, p⟩ₖ ∈ R → ∃ r ∈ P, ⟨r, q⟩ₖ ∈ R ∧
        (ForcingTableHolds T n φ b r ∨ ForcingTableHolds T n ψ b r) := by
  simp [boundedForcingOrBody, Matrix.comp_vecCons', Function.comp_def, Matrix.constant_eq_singleton]
  apply forall_congr'
  intro q
  apply imp_congr_right
  intro _
  apply imp_congr_right
  intro _
  apply exists_congr
  intro r
  apply and_congr_right
  intro hr
  rw [CodeExpression.eval_forcingLookupFormula_two _ T hb (hP r hr) hn hφ,
    CodeExpression.eval_forcingLookupFormula_two _ T hb (hP r hr) hn hψ]
  rfl

theorem eval_boundedForcingBooleanClause {U P n b p φ ψ : V} [IsCodingSupport U]
    (hP : P ⊆ U) (hn : n ∈ U) (hb : b ∈ U) (hp : p ∈ U)
    (hφ : φ ∈ U) (hψ : ψ ∈ U) (R T : V) :
    boundedForcingBooleanClause.Evalb ![U, P, R, T, n, b, p, φ, ψ] ↔
      (ForcingTableHolds T n (andCode φ ψ) b p ↔ ForcingTableHolds T n φ b p ∧ ForcingTableHolds T n ψ b p) ∧
      (ForcingTableHolds T n (orCode φ ψ) b p ↔ ∀ q ∈ P, ⟨q, p⟩ₖ ∈ R →
        ∃ r ∈ P, ⟨r, q⟩ₖ ∈ R ∧ (ForcingTableHolds T n φ b r ∨ ForcingTableHolds T n ψ b r)) := by
  simp [boundedForcingBooleanClause, Matrix.comp_vecCons', Function.comp_def, Matrix.constant_eq_singleton]
  rw [CodeExpression.eval_forcingLookupFormula_three _ T hb hp hn hφ hψ,
    CodeExpression.eval_forcingLookupFormula_three _ T hb hp hn hφ hψ,
    CodeExpression.eval_forcingLookupFormula_two _ T hb hp hn hφ,
    CodeExpression.eval_forcingLookupFormula_two _ T hb hp hn hψ,
    eval_boundedForcingOrBody hP hn hb hφ hψ]
  rfl

end ZFVP
