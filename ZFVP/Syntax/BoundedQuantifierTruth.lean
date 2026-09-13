import ZFVP.Syntax.BoundedTruthClauses
import ZFVP.Syntax.BoundedAssignments

/-! Bounded truth-table checks for guarded quantifiers. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def boundedTruthPrependLookupFormula : SetTheorySemisentence 7 :=
  “U O T n b x φ. ∃ c ∈ U, !boundedAssignmentPrependFormula U O c n b x ∧
    !(CodeExpression.kpair (.succ (.var 0)) (.var 1)).lookupFormula U T c n φ”

def boundedAllTruthBodyFormula : SetTheorySemisentence 7 :=
  “U O T n b i φ. ∃ y ∈ U, !boundedPairMemberFormula b i y ∧
    ∀ x ∈ y, !boundedTruthPrependLookupFormula U O T n b x φ”

def boundedExistsTruthBodyFormula : SetTheorySemisentence 7 :=
  “U O T n b i φ. ∃ y ∈ U, !boundedPairMemberFormula b i y ∧
    ∃ x ∈ y, !boundedTruthPrependLookupFormula U O T n b x φ”

def boundedQuantifierTruthClause : SetTheorySemisentence 7 :=
  “U O T n b i φ.
    (!(CodeExpression.kpair (.var 0) (.boundedAll (.var 1) (.var 2))).lookupFormula U T b n i φ ↔
      !boundedAllTruthBodyFormula U O T n b i φ) ∧
    (!(CodeExpression.kpair (.var 0) (.boundedExs (.var 1) (.var 2))).lookupFormula U T b n i φ ↔
      !boundedExistsTruthBodyFormula U O T n b i φ)”

theorem boundedTruthPrependLookupFormula_bounded : IsBoundedSetFormula boundedTruthPrependLookupFormula :=
  .exs (.bvar 0) (.and (boundedAssignmentPrependFormula_bounded.subst _)
    ((CodeExpression.kpair (.succ (.var 0)) (.var 1)).lookupFormula_bounded.subst _))

theorem boundedAllTruthBodyFormula_bounded : IsBoundedSetFormula boundedAllTruthBodyFormula :=
  .exs (.bvar 0) (.and (boundedPairMemberFormula_bounded.subst _)
    (.all (.bvar 0) (boundedTruthPrependLookupFormula_bounded.subst _)))

theorem boundedExistsTruthBodyFormula_bounded : IsBoundedSetFormula boundedExistsTruthBodyFormula :=
  .exs (.bvar 0) (.and (boundedPairMemberFormula_bounded.subst _)
    (.exs (.bvar 0) (boundedTruthPrependLookupFormula_bounded.subst _)))

theorem boundedQuantifierTruthClause_bounded : IsBoundedSetFormula boundedQuantifierTruthClause :=
  .and (((CodeExpression.kpair (.var 0) (.boundedAll (.var 1) (.var 2))).lookupFormula_bounded.subst _).iff
    (boundedAllTruthBodyFormula_bounded.subst _))
    (((CodeExpression.kpair (.var 0) (.boundedExs (.var 1) (.var 2))).lookupFormula_bounded.subst _).iff
      (boundedExistsTruthBodyFormula_bounded.subst _))

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem eval_boundedTruthPrependLookupFormula {U A n b x φ : V} [IsSequenceSupport U]
    (hA : A ⊆ U) (hn : n ∈ (ω : V)) (hb : b ∈ A ^ n) (hx : x ∈ A) (hφ : φ ∈ U) (T : V) :
    boundedTruthPrependLookupFormula.Evalb ![U, ω, T, n, b, x, φ] ↔
      TableHolds T (succ n) φ (assignmentPrepend n b x) := by
  have hbU := mem_function_of_mem_function_of_subset hb hA
  have hpre := assignmentPrepend_mem_function hn hb hx
  have hcU := function_mem_sequenceSupport hA (ω_succ_closed hn) hpre
  simp [boundedTruthPrependLookupFormula, Matrix.comp_vecCons', Function.comp_def, Matrix.constant_eq_singleton]
  simp only [eval_boundedAssignmentPrependFormula hn hbU (hA x hx)]
  have he : (CodeExpression.kpair (.succ (.var 0)) (.var 1)).lookupFormula.Evalb
      ![U, T, assignmentPrepend n b x, n, φ] ↔ TableHolds T (succ n) φ (assignmentPrepend n b x) := by
    rw [CodeExpression.eval_lookupFormula_two _ T _ (IsCodingSupport.natural_mem hn) hφ]
    simp [CodeExpression.eval, TableHolds]
  exact ⟨fun ⟨_, _, h, hp⟩ ↦ he.mp (h ▸ hp), fun h ↦ ⟨_, hcU, rfl, he.mpr h⟩⟩

theorem eval_boundedAllTruthBodyFormula {U A n b i φ : V} [IsSequenceSupport U] [hAt : IsTransitive A]
    (hA : A ⊆ U) (hn : n ∈ (ω : V)) (hb : b ∈ A ^ n) (hi : i ∈ n) (hφ : φ ∈ U) (T : V) :
    boundedAllTruthBodyFormula.Evalb ![U, ω, T, n, b, i, φ] ↔
      ∀ x ∈ b ‘ i, TableHolds T (succ n) φ (assignmentPrepend n b x) := by
  have : IsFunction b := IsFunction.of_mem hb
  have hyU := hA _ (function_value_mem hb hi)
  simp [boundedAllTruthBodyFormula, Matrix.comp_vecCons', Function.comp_def, Matrix.constant_eq_singleton,
    kpair_mem_iff_value, domain_eq_of_mem_function hb, hi, hyU]
  exact forall_congr' fun x ↦ imp_congr_right fun hx ↦
    eval_boundedTruthPrependLookupFormula hA hn hb (hAt.mem_trans hx (function_value_mem hb hi)) hφ T

theorem eval_boundedExistsTruthBodyFormula {U A n b i φ : V} [IsSequenceSupport U] [hAt : IsTransitive A]
    (hA : A ⊆ U) (hn : n ∈ (ω : V)) (hb : b ∈ A ^ n) (hi : i ∈ n) (hφ : φ ∈ U) (T : V) :
    boundedExistsTruthBodyFormula.Evalb ![U, ω, T, n, b, i, φ] ↔
      ∃ x ∈ b ‘ i, TableHolds T (succ n) φ (assignmentPrepend n b x) := by
  have : IsFunction b := IsFunction.of_mem hb
  have hyU := hA _ (function_value_mem hb hi)
  simp [boundedExistsTruthBodyFormula, Matrix.comp_vecCons', Function.comp_def, Matrix.constant_eq_singleton,
    kpair_mem_iff_value, domain_eq_of_mem_function hb, hi, hyU]
  exact exists_congr fun x ↦ and_congr_right fun hx ↦
    eval_boundedTruthPrependLookupFormula hA hn hb (hAt.mem_trans hx (function_value_mem hb hi)) hφ T

theorem eval_boundedQuantifierTruthClause {U A n b i φ : V} [IsSequenceSupport U] [IsTransitive A]
    (hA : A ⊆ U) (hn : n ∈ (ω : V)) (hb : b ∈ A ^ n) (hi : i ∈ n) (hφ : φ ∈ U) (T : V) :
    boundedQuantifierTruthClause.Evalb ![U, ω, T, n, b, i, φ] ↔
      (TableHolds T n (boundedAllCode i φ) b ↔ ∀ x ∈ b ‘ i, TableHolds T (succ n) φ (assignmentPrepend n b x)) ∧
      (TableHolds T n (boundedExistsCode i φ) b ↔ ∃ x ∈ b ‘ i, TableHolds T (succ n) φ (assignmentPrepend n b x)) := by
  have hnU : n ∈ U := IsCodingSupport.natural_mem hn
  have hiU : i ∈ U := (inferInstance : IsTransitive U).mem_trans hi hnU
  simp [boundedQuantifierTruthClause, Matrix.comp_vecCons', Function.comp_def, Matrix.constant_eq_singleton]
  rw [CodeExpression.eval_lookupFormula_three _ T b hnU hiU hφ,
    CodeExpression.eval_lookupFormula_three _ T b hnU hiU hφ,
    eval_boundedAllTruthBodyFormula hA hn hb hi hφ, eval_boundedExistsTruthBodyFormula hA hn hb hi hφ]
  simp [CodeExpression.eval, TableHolds]

end ZFVP
