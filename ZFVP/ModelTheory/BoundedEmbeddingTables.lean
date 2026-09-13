import ZFVP.ModelTheory.PiOneMembershipEmbedding

/-! Bounded comparison of complete membership truth tables along an embedding graph. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def boundedEmbeddingTablesFormula : SetTheorySemisentence 8 :=
  “U O F A B f T S. ∀ n ∈ O, ∀ φ ∈ U, ∀ b ∈ U, ∀ c ∈ U,
    !boundedPairMemberFormula F n φ → !boundedFunctionFormula b n A →
      !boundedComposedAssignmentFormula n A B b f c →
        (!(boundedTableAnswerFormula true) U T n φ b ↔ !(boundedTableAnswerFormula true) U S n φ c)”

theorem boundedEmbeddingTablesFormula_bounded : IsBoundedSetFormula boundedEmbeddingTablesFormula :=
  .all (.bvar 1) (.all (.bvar 1) (.all (.bvar 2) (.all (.bvar 3)
    (.or (boundedPairMemberFormula_bounded.subst _).neg
      (.or (boundedFunctionFormula_bounded.subst _).neg
        (.or (boundedComposedAssignmentFormula_bounded.subst _).neg
          (.and
            (.or ((boundedTableAnswerFormula_bounded true).subst _).neg
              ((boundedTableAnswerFormula_bounded true).subst _))
            (.or ((boundedTableAnswerFormula_bounded true).subst _).neg
              ((boundedTableAnswerFormula_bounded true).subst _)))))))))

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem eval_truthTableAnswer {U A T n φ b : V} [IsSequenceSupport U]
    (hT : IsMembershipTruthTable A T) (hφ : IsMembershipFormulaCode n φ) (hb : b ∈ A ^ n) :
    (boundedTableAnswerFormula true).Evalb ![U, T, n, φ, b] ↔ MembershipSatisfies A n φ b :=
  (eval_boundedTableAnswerFormula true (IsCodingSupport.natural_mem hφ.context)
    (membershipFormulaCode_formula_mem_support hφ) T b).trans (membershipTruthTable_correct hT hφ hb)

theorem eval_boundedEmbeddingTablesFormula {U A B f T S : V} [IsSequenceSupport U]
    (hA : A ⊆ U) (hB : B ⊆ U) (hf : f ∈ B ^ A)
    (hT : IsMembershipTruthTable A T) (hS : IsMembershipTruthTable B S) :
    boundedEmbeddingTablesFormula.Evalb ![U, ω, formulaFamily membershipLanguageCode ∅, A, B, f, T, S] ↔
      ∀ n φ b, IsMembershipFormulaCode n φ → b ∈ A ^ n →
        (MembershipSatisfies A n φ b ↔ MembershipSatisfies B n φ (compose b f)) := by
  simp [boundedEmbeddingTablesFormula, Matrix.comp_vecCons', Function.comp_def, Matrix.constant_eq_singleton]
  constructor
  · intro h n φ b hφ hb
    have hc := compose_function hb hf
    have hcomp := (isComposedAssignment_iff hb hf).mpr rfl
    have ht := h n hφ.context φ (membershipFormulaCode_formula_mem_support hφ)
      b (function_mem_sequenceSupport hA hφ.context hb)
      (compose b f) (function_mem_sequenceSupport hB hφ.context hc) hφ hb hcomp
    rw [eval_truthTableAnswer hT hφ hb, eval_truthTableAnswer hS hφ hc] at ht
    exact ht
  · intro h n hn φ hφU b hbU c hcU hφ hb hc
    have hceq := (isComposedAssignment_iff hb hf).mp hc
    rw [hceq, eval_truthTableAnswer hT hφ hb,
      eval_truthTableAnswer hS hφ (compose_function hb hf)]
    exact h n φ b hφ hb

end ZFVP
