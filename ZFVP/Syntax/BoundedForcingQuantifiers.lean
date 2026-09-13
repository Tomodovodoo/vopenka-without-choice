import ZFVP.Syntax.BoundedForcingClauses
import ZFVP.Syntax.BoundedAssignments

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

def boundedForcingPrependLookup : SetTheorySemisentence 8 :=
  “U O T n b x p φ. ∃ c ∈ U, !boundedAssignmentPrependFormula U O c n b x ∧
    !(CodeExpression.kpair (.succ (.var 0)) (.var 1)).forcingLookupFormula U T c p n φ”

def boundedForcingAllBody : SetTheorySemisentence 8 :=
  “U O D T n b p φ. ∀ x ∈ D, !boundedForcingPrependLookup U O T n b x p φ”

def boundedForcingExistsBody : SetTheorySemisentence 10 :=
  “U O P R D T n b p φ. ∀ q ∈ P, !boundedPairMemberFormula R q p →
    ∃ r ∈ P, !boundedPairMemberFormula R r q ∧
      ∃ x ∈ D, !boundedForcingPrependLookup U O T n b x r φ”

def boundedForcingQuantifierClause : SetTheorySemisentence 10 :=
  “U O P R D T n b p φ.
    (!(CodeExpression.kpair (.var 0) (.all (.var 1))).forcingLookupFormula U T b p n φ ↔
      !boundedForcingAllBody U O D T n b p φ) ∧
    (!(CodeExpression.kpair (.var 0) (.exs (.var 1))).forcingLookupFormula U T b p n φ ↔
      !boundedForcingExistsBody U O P R D T n b p φ)”

theorem boundedForcingPrependLookup_bounded : IsBoundedSetFormula boundedForcingPrependLookup :=
  .exs (.bvar 0) (.and (boundedAssignmentPrependFormula_bounded.subst _)
    ((CodeExpression.kpair (.succ (.var 0)) (.var 1)).forcingLookupFormula_bounded.subst _))

theorem boundedForcingAllBody_bounded : IsBoundedSetFormula boundedForcingAllBody :=
  .all (.bvar 2) (boundedForcingPrependLookup_bounded.subst _)

theorem boundedForcingExistsBody_bounded : IsBoundedSetFormula boundedForcingExistsBody := by
  repeat' first
    | exact boundedForcingPrependLookup_bounded.subst _
    | exact boundedPairMemberFormula_bounded.subst _
    | exact (boundedPairMemberFormula_bounded.subst _).neg
    | apply IsBoundedSetFormula.all
    | apply IsBoundedSetFormula.exs
    | apply IsBoundedSetFormula.and
    | apply IsBoundedSetFormula.or

theorem boundedForcingQuantifierClause_bounded : IsBoundedSetFormula boundedForcingQuantifierClause :=
  .and (((CodeExpression.kpair (.var 0) (.all (.var 1))).forcingLookupFormula_bounded.subst _).iff
    (boundedForcingAllBody_bounded.subst _))
    (((CodeExpression.kpair (.var 0) (.exs (.var 1))).forcingLookupFormula_bounded.subst _).iff
      (boundedForcingExistsBody_bounded.subst _))

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem eval_boundedForcingPrependLookup {U D n b x p φ : V} [IsSequenceSupport U]
    (hD : D ⊆ U) (hn : n ∈ (ω : V)) (hb : b ∈ D ^ n) (hx : x ∈ D)
    (hp : p ∈ U) (hφ : φ ∈ U) (T : V) :
    boundedForcingPrependLookup.Evalb ![U, ω, T, n, b, x, p, φ] ↔
      ForcingTableHolds T (succ n) φ (assignmentPrepend n b x) p := by
  have hbU := mem_function_of_mem_function_of_subset hb hD
  have hcU := function_mem_sequenceSupport hD (ω_succ_closed hn) (assignmentPrepend_mem_function hn hb hx)
  simp [boundedForcingPrependLookup, Matrix.comp_vecCons', Function.comp_def, Matrix.constant_eq_singleton]
  simp only [eval_boundedAssignmentPrependFormula hn hbU (hD x hx)]
  have he : (CodeExpression.kpair (.succ (.var 0)) (.var 1)).forcingLookupFormula.Evalb
      ![U, T, assignmentPrepend n b x, p, n, φ] ↔
        ForcingTableHolds T (succ n) φ (assignmentPrepend n b x) p := by
    rw [CodeExpression.eval_forcingLookupFormula_two _ T hcU hp (IsCodingSupport.natural_mem hn) hφ]
    rfl
  exact ⟨fun ⟨_, _, h, ht⟩ ↦ he.mp (h ▸ ht), fun h ↦ ⟨_, hcU, rfl, he.mpr h⟩⟩

theorem eval_boundedForcingAllBody {U D n b p φ : V} [IsSequenceSupport U]
    (hD : D ⊆ U) (hn : n ∈ (ω : V)) (hb : b ∈ D ^ n) (hp : p ∈ U) (hφ : φ ∈ U) (T : V) :
    boundedForcingAllBody.Evalb ![U, ω, D, T, n, b, p, φ] ↔
      ∀ x ∈ D, ForcingTableHolds T (succ n) φ (assignmentPrepend n b x) p := by
  simp [boundedForcingAllBody, Matrix.comp_vecCons', Function.comp_def, Matrix.constant_eq_singleton]
  exact forall_congr' fun x ↦ imp_congr_right fun hx ↦ eval_boundedForcingPrependLookup hD hn hb hx hp hφ T

theorem eval_boundedForcingExistsBody {U P D n b p φ : V} [IsSequenceSupport U]
    (hP : P ⊆ U) (hD : D ⊆ U) (hn : n ∈ (ω : V)) (hb : b ∈ D ^ n) (hφ : φ ∈ U) (R T : V) :
    boundedForcingExistsBody.Evalb ![U, ω, P, R, D, T, n, b, p, φ] ↔
      ∀ q ∈ P, ⟨q, p⟩ₖ ∈ R → ∃ r ∈ P, ⟨r, q⟩ₖ ∈ R ∧
        ∃ x ∈ D, ForcingTableHolds T (succ n) φ (assignmentPrepend n b x) r := by
  simp [boundedForcingExistsBody, Matrix.comp_vecCons', Function.comp_def, Matrix.constant_eq_singleton]
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
  apply and_congr Iff.rfl
  exact exists_congr fun x ↦ and_congr_right fun hx ↦ eval_boundedForcingPrependLookup hD hn hb hx (hP r hr) hφ T

theorem eval_boundedForcingQuantifierClause {U P D n b p φ : V} [IsSequenceSupport U]
    (hP : P ⊆ U) (hD : D ⊆ U) (hn : n ∈ (ω : V)) (hb : b ∈ D ^ n)
    (hp : p ∈ U) (hφ : φ ∈ U) (R T : V) :
    boundedForcingQuantifierClause.Evalb ![U, ω, P, R, D, T, n, b, p, φ] ↔
      (ForcingTableHolds T n (allCode φ) b p ↔
        ∀ x ∈ D, ForcingTableHolds T (succ n) φ (assignmentPrepend n b x) p) ∧
      (ForcingTableHolds T n (existsCode φ) b p ↔ ∀ q ∈ P, ⟨q, p⟩ₖ ∈ R →
        ∃ r ∈ P, ⟨r, q⟩ₖ ∈ R ∧ ∃ x ∈ D, ForcingTableHolds T (succ n) φ (assignmentPrepend n b x) r) := by
  have hnU : n ∈ U := IsCodingSupport.natural_mem hn
  have hbU := function_mem_sequenceSupport hD hn hb
  simp [boundedForcingQuantifierClause, Matrix.comp_vecCons', Function.comp_def, Matrix.constant_eq_singleton]
  rw [CodeExpression.eval_forcingLookupFormula_two _ T hbU hp hnU hφ,
    CodeExpression.eval_forcingLookupFormula_two _ T hbU hp hnU hφ,
    eval_boundedForcingAllBody hD hn hb hp hφ, eval_boundedForcingExistsBody hP hD hn hb hφ]
  rfl

end ZFVP
