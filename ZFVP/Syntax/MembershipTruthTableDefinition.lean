import ZFVP.Syntax.BoundedTruthTableDefinition
import ZFVP.Syntax.MembershipQuantifierTruth

/-! A bounded formula checks all constructor equations of a membership truth table. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def membershipTableAtAssignmentFormula : SetTheorySemisentence 7 :=
  “U O F T n b A. !boundedConstantTruthClause U T n b ∧
    (∀ r ∈ U, ∀ args ∈ U, !boundedAtomicArgumentsFormula U n r args → !boundedAtomicTruthClause U T n b r args) ∧
    (∀ φ ∈ U, ∀ ψ ∈ U, !boundedPairMemberFormula F n φ → !boundedPairMemberFormula F n ψ →
      !boundedBooleanTruthClause U T n b φ ψ) ∧
    ∀ φ ∈ U, !boundedSuccessorContextFormula U F n φ → !membershipQuantifierTruthClause U O T n b A φ”

def membershipTruthTableFormula : SetTheorySemisentence 5 :=
  “U O F A T. ∀ n ∈ O, ∀ b ∈ U, !boundedFunctionFormula b n A → !membershipTableAtAssignmentFormula U O F T n b A”

theorem membershipTableAtAssignmentFormula_bounded : IsBoundedSetFormula membershipTableAtAssignmentFormula :=
  .and (boundedConstantTruthClause_bounded.subst _)
    (.and (.all (.bvar 0) (.all (.bvar 1) (.or (boundedAtomicArgumentsFormula_bounded.subst _).neg
      (boundedAtomicTruthClause_bounded.subst _))))
      (.and (.all (.bvar 0) (.all (.bvar 1) (.or (boundedPairMemberFormula_bounded.subst _).neg
        (.or (boundedPairMemberFormula_bounded.subst _).neg (boundedBooleanTruthClause_bounded.subst _)))))
        (.all (.bvar 0) (.or (boundedSuccessorContextFormula_bounded.subst _).neg
          (membershipQuantifierTruthClause_bounded.subst _)))))

theorem membershipTruthTableFormula_bounded : IsBoundedSetFormula membershipTruthTableFormula :=
  .all (.bvar 1) (.all (.bvar 1) (.or (boundedFunctionFormula_bounded.subst _).neg
    (membershipTableAtAssignmentFormula_bounded.subst _)))

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem membershipFormulaCode_formula_mem_support {U n φ : V} [IsCodingSupport U]
    (hφ : IsMembershipFormulaCode n φ) : φ ∈ U :=
  (kpair_components_mem_transitive (membershipFormulaFamily_subset_support U _ hφ)).2

theorem eval_membershipTableAtAssignmentFormula {U A n b : V} [IsSequenceSupport U] 
    (hA : A ⊆ U) (hn : n ∈ (ω : V)) (hb : b ∈ A ^ n) (T : V) :
    membershipTableAtAssignmentFormula.Evalb ![U, ω, formulaFamily membershipLanguageCode ∅, T, n, b, A] ↔ MembershipTruthClauses A T n b := by
  have hnU : n ∈ U := IsCodingSupport.natural_mem hn
  have hbU := mem_function_of_mem_function_of_subset hb hA
  simp [membershipTableAtAssignmentFormula, MembershipTruthClauses,
    Matrix.comp_vecCons', Function.comp_def, Matrix.constant_eq_singleton]
  rw [eval_boundedConstantTruthClause hnU]
  apply and_congr_right
  intro _
  constructor
  · rintro ⟨ha, hbool, hquant⟩
    refine ⟨?_, ?_, ?_⟩
    · intro r args hargs
      obtain ⟨hrU, haU⟩ := membershipAtomicArguments_mem_support (U := U) hn ((membershipAtomicArguments_iff hn).mpr hargs)
      exact (eval_boundedAtomicTruthClause hnU hbU hrU haU T).mp
        (ha r hrU args haU ((eval_boundedAtomicArgumentsFormula hnU r args).mpr hargs))
    · intro φ ψ hφ hψ
      have hφU := membershipFormulaCode_formula_mem_support (U := U) hφ
      have hψU := membershipFormulaCode_formula_mem_support (U := U) hψ
      exact (eval_boundedBooleanTruthClause hnU hφU hψU T b).mp (hbool φ hφU ψ hψU hφ hψ)
    · intro φ hφ
      have hφU := membershipFormulaCode_formula_mem_support (U := U) hφ
      exact (eval_membershipQuantifierTruthClause hA hn hb hφU T).mp
        (hquant φ hφU ((eval_boundedSuccessorContextFormula hnU _ φ).mpr hφ))
  · rintro ⟨ha, hbool, hquant⟩
    refine ⟨?_, ?_, ?_⟩
    · intro r hrU args haU hargs
      exact (eval_boundedAtomicTruthClause hnU hbU hrU haU T).mpr
        (ha r args ((eval_boundedAtomicArgumentsFormula hnU r args).mp hargs))
    · intro φ hφU ψ hψU hφ hψ
      exact (eval_boundedBooleanTruthClause hnU hφU hψU T b).mpr (hbool φ ψ hφ hψ)
    · intro φ hφU hφ
      exact (eval_membershipQuantifierTruthClause hA hn hb hφU T).mpr
        (hquant φ ((eval_boundedSuccessorContextFormula hnU _ φ).mp hφ))

theorem eval_membershipTruthTableFormula {U A : V} [IsSequenceSupport U] 
    (hA : A ⊆ U) (T : V) :
    membershipTruthTableFormula.Evalb ![U, ω, formulaFamily membershipLanguageCode ∅, A, T] ↔ IsMembershipTruthTable A T := by
  simp [membershipTruthTableFormula, IsMembershipTruthTable,
    Matrix.comp_vecCons', Function.comp_def, Matrix.constant_eq_singleton]
  constructor
  · intro h n hn b hb
    exact (eval_membershipTableAtAssignmentFormula hA hn hb T).mp
      (h n hn b (function_mem_sequenceSupport hA hn hb) hb)
  · intro h n hn b _ hb
    exact (eval_membershipTableAtAssignmentFormula hA hn hb T).mpr (h n hn b hb)

end ZFVP
