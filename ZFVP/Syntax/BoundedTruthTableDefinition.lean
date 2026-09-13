import ZFVP.Syntax.BoundedQuantifierTruth
import ZFVP.Syntax.CodingSupportSyntax
import ZFVP.Syntax.BoundedAtomicDefinition

/-! A bounded formula checks all constructor equations of a bounded truth table. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def boundedSuccessorContextFormula : SetTheorySemisentence 4 :=
  “U F n φ. ∃ m ∈ U, !boundedSuccFormula m n ∧ !boundedPairMemberFormula F m φ”

def boundedTableAtAssignmentFormula : SetTheorySemisentence 6 :=
  “U O F T n b. !boundedConstantTruthClause U T n b ∧
    (∀ r ∈ U, ∀ args ∈ U, !boundedAtomicArgumentsFormula U n r args → !boundedAtomicTruthClause U T n b r args) ∧
    (∀ φ ∈ U, ∀ ψ ∈ U, !boundedPairMemberFormula F n φ → !boundedPairMemberFormula F n ψ →
      !boundedBooleanTruthClause U T n b φ ψ) ∧
    ∀ i ∈ n, ∀ φ ∈ U, !boundedSuccessorContextFormula U F n φ → !boundedQuantifierTruthClause U O T n b i φ”

def boundedTruthTableFormula : SetTheorySemisentence 5 :=
  “U O F A T. ∀ n ∈ O, ∀ b ∈ U, !boundedFunctionFormula b n A → !boundedTableAtAssignmentFormula U O F T n b”

theorem boundedSuccessorContextFormula_bounded : IsBoundedSetFormula boundedSuccessorContextFormula :=
  .exs (.bvar 0) (.and (boundedSuccFormula_bounded.subst _) (boundedPairMemberFormula_bounded.subst _))

theorem boundedTableAtAssignmentFormula_bounded : IsBoundedSetFormula boundedTableAtAssignmentFormula :=
  .and (boundedConstantTruthClause_bounded.subst _)
    (.and (.all (.bvar 0) (.all (.bvar 1) (.or (boundedAtomicArgumentsFormula_bounded.subst _).neg
      (boundedAtomicTruthClause_bounded.subst _))))
      (.and (.all (.bvar 0) (.all (.bvar 1) (.or (boundedPairMemberFormula_bounded.subst _).neg
        (.or (boundedPairMemberFormula_bounded.subst _).neg (boundedBooleanTruthClause_bounded.subst _)))))
        (.all (.bvar 4) (.all (.bvar 1) (.or (boundedSuccessorContextFormula_bounded.subst _).neg
          (boundedQuantifierTruthClause_bounded.subst _))))))

theorem boundedTruthTableFormula_bounded : IsBoundedSetFormula boundedTruthTableFormula :=
  .all (.bvar 1) (.all (.bvar 1) (.or (boundedFunctionFormula_bounded.subst _).neg
    (boundedTableAtAssignmentFormula_bounded.subst _)))

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem eval_boundedSuccessorContextFormula {U n : V} [hU : IsCodingSupport U] (hn : n ∈ U) (F φ : V) :
    boundedSuccessorContextFormula.Evalb ![U, F, n, φ] ↔ ⟨succ n, φ⟩ₖ ∈ F := by
  simp [boundedSuccessorContextFormula, hU.succ_closed n hn]

theorem boundedFormulaCode_formula_mem_support {U n φ : V} [IsCodingSupport U]
    (hφ : IsBoundedFormulaCode n φ) : φ ∈ U :=
  (kpair_components_mem_transitive (boundedFormulaFamily_subset_support U _ hφ)).2

theorem eval_boundedTableAtAssignmentFormula {U A n b : V} [IsSequenceSupport U] [IsTransitive A]
    (hA : A ⊆ U) (hn : n ∈ (ω : V)) (hb : b ∈ A ^ n) (T : V) :
    boundedTableAtAssignmentFormula.Evalb ![U, ω, boundedFormulaFamily, T, n, b] ↔ BoundedTruthClauses T n b := by
  have hnU : n ∈ U := IsCodingSupport.natural_mem hn
  have hbU := mem_function_of_mem_function_of_subset hb hA
  simp [boundedTableAtAssignmentFormula, BoundedTruthClauses,
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
      have hφU := boundedFormulaCode_formula_mem_support (U := U) hφ
      have hψU := boundedFormulaCode_formula_mem_support (U := U) hψ
      exact (eval_boundedBooleanTruthClause hnU hφU hψU T b).mp (hbool φ hφU ψ hψU hφ hψ)
    · intro i hi φ hφ
      have hφU := boundedFormulaCode_formula_mem_support (U := U) hφ
      exact (eval_boundedQuantifierTruthClause hA hn hb hi hφU T).mp
        (hquant i hi φ hφU ((eval_boundedSuccessorContextFormula hnU _ φ).mpr hφ))
  · rintro ⟨ha, hbool, hquant⟩
    refine ⟨?_, ?_, ?_⟩
    · intro r hrU args haU hargs
      exact (eval_boundedAtomicTruthClause hnU hbU hrU haU T).mpr
        (ha r args ((eval_boundedAtomicArgumentsFormula hnU r args).mp hargs))
    · intro φ hφU ψ hψU hφ hψ
      exact (eval_boundedBooleanTruthClause hnU hφU hψU T b).mpr (hbool φ ψ hφ hψ)
    · intro i hi φ hφU hφ
      exact (eval_boundedQuantifierTruthClause hA hn hb hi hφU T).mpr
        (hquant i hi φ ((eval_boundedSuccessorContextFormula hnU _ φ).mp hφ))

theorem eval_boundedTruthTableFormula {U A : V} [IsSequenceSupport U] [IsTransitive A]
    (hA : A ⊆ U) (T : V) :
    boundedTruthTableFormula.Evalb ![U, ω, boundedFormulaFamily, A, T] ↔ IsBoundedTruthTable A T := by
  simp [boundedTruthTableFormula, IsBoundedTruthTable,
    Matrix.comp_vecCons', Function.comp_def, Matrix.constant_eq_singleton]
  constructor
  · intro h n hn b hb
    exact (eval_boundedTableAtAssignmentFormula hA hn hb T).mp
      (h n hn b (function_mem_sequenceSupport hA hn hb) hb)
  · intro h n hn b _ hb
    exact (eval_boundedTableAtAssignmentFormula hA hn hb T).mpr (h n hn b hb)

end ZFVP
