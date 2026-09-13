import ZFVP.Syntax.BoundedTruthTableDefinition
import ZFVP.Syntax.SigmaOneBoundedFamily

/-! Existential bounded certificates for truth and falsity in transitive set domains. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def TruthAnswer (answer : Bool) (P : Prop) : Prop := if answer then P else ¬P

def boundedTablePositiveFormula : SetTheorySemisentence 5 :=
  “U T n φ b. !(CodeExpression.kpair (.var 0) (.var 1)).lookupFormula U T b n φ”

def boundedTableAnswerFormula (answer : Bool) : SetTheorySemisentence 5 :=
  if answer then boundedTablePositiveFormula else ∼boundedTablePositiveFormula

def sigmaOneBoundedModelTruthFormula (answer : Bool) : SetTheorySemisentence 4 :=
  “A n φ b. !IsTransitive.dfn A ∧ ∃ F, !sigmaOneBoundedFamilyFormula F ∧
    !boundedPairMemberFormula F n φ ∧ !boundedFunctionFormula b n A ∧
    ∃ U, !sequenceSupportFormula U ∧ A ∈ U ∧ ∃ O ∈ U, !boundedOmegaFormula O ∧
      ∃ T, !boundedTruthTableFormula U O F A T ∧ !(boundedTableAnswerFormula answer) U T n φ b”

theorem boundedTableAnswerFormula_bounded (answer : Bool) : IsBoundedSetFormula (boundedTableAnswerFormula answer) := by
  cases answer
  · exact ((CodeExpression.kpair (.var 0) (.var 1)).lookupFormula_bounded.subst _).neg
  · exact (CodeExpression.kpair (.var 0) (.var 1)).lookupFormula_bounded.subst _

theorem sigmaOneBoundedModelTruthFormula_sigmaOne (answer : Bool) :
    IsLevyFormula .sigma 1 (sigmaOneBoundedModelTruthFormula answer) := by
  refine .and (.bounded (isTransitiveFormula_bounded.subst _)) (.exs (.and (sigmaOneBoundedFamilyFormula_sigmaOne.subst _) ?_))
  refine .and (.bounded (boundedPairMemberFormula_bounded.subst _))
    (.and (.bounded (boundedFunctionFormula_bounded.subst _)) (.exs ?_))
  refine .and (.bounded (sequenceSupportFormula_bounded.subst _))
    (.and (.bounded (.rel _ _)) (.boundedExs (.bvar 0) ?_))
  exact .and (.bounded (boundedOmegaFormula_bounded.subst _))
    (.exs (.and (.bounded (boundedTruthTableFormula_bounded.subst _))
      (.bounded ((boundedTableAnswerFormula_bounded answer).subst _))))

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem eval_boundedTableAnswerFormula (answer : Bool) {U n φ : V} [IsCodingSupport U]
    (hn : n ∈ U) (hφ : φ ∈ U) (T b : V) :
    (boundedTableAnswerFormula answer).Evalb ![U, T, n, φ, b] ↔ TruthAnswer answer (TableHolds T n φ b) := by
  cases answer <;>
    simp [boundedTableAnswerFormula, boundedTablePositiveFormula, TruthAnswer, Matrix.comp_vecCons', Function.comp_def, Matrix.constant_eq_singleton,
      hn, hφ, CodeExpression.eval, TableHolds]

theorem truthAnswer_congr (answer : Bool) {P Q : Prop} (h : P ↔ Q) : TruthAnswer answer P ↔ TruthAnswer answer Q := by
  cases answer
  · exact not_congr h
  · exact h

theorem eval_sigmaOneBoundedModelTruthFormula (answer : Bool) (A n φ b : V) :
    (sigmaOneBoundedModelTruthFormula answer).Evalb ![A, n, φ, b] ↔
      IsTransitive A ∧ IsBoundedFormulaCode n φ ∧ b ∈ A ^ n ∧ TruthAnswer answer (MembershipSatisfies A n φ b) := by
  simp [sigmaOneBoundedModelTruthFormula, Matrix.comp_vecCons', Function.comp_def, Matrix.constant_eq_singleton,
    IsBoundedFormulaCode]
  intro hAt
  let := hAt
  intro hφ hb
  have hn : n ∈ (ω : V) := IsBoundedFormulaCode.context hφ
  constructor
  · rintro ⟨U, hU, hA, hω, T, hT, hanswer⟩
    let := hU
    have hAU : A ⊆ U := hU.transitive A hA
    have hT' := (eval_boundedTruthTableFormula hAU T).mp hT
    have hanswer' := (eval_boundedTableAnswerFormula answer (IsCodingSupport.natural_mem hn)
      (boundedFormulaCode_formula_mem_support hφ) T b).mp hanswer
    exact (truthAnswer_congr answer (boundedTruthTable_correct hT' hφ hb)).mp hanswer'
  · intro hanswer
    obtain ⟨U, hU, hA⟩ := sequenceSupport_containing A
    let := hU
    have hAU : A ⊆ U := hU.transitive A hA
    refine ⟨U, hU, hA, hU.omega_mem, boundedModelTruthTable A,
      (eval_boundedTruthTableFormula hAU _).mpr (boundedModelTruthTable_correct A), ?_⟩
    apply (eval_boundedTableAnswerFormula answer (IsCodingSupport.natural_mem hn)
      (boundedFormulaCode_formula_mem_support hφ) _ b).mpr
    exact (truthAnswer_congr answer (boundedModelTruthTable_lookup hφ hb)).mpr hanswer

end ZFVP
