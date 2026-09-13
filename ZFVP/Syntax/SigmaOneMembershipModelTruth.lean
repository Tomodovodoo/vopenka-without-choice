import ZFVP.Syntax.MembershipTruthTableDefinition
import ZFVP.Syntax.SigmaOneBoundedModelTruth

/-! Existential bounded certificates for truth and falsity in arbitrary set domains. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def sigmaOneMembershipModelTruthFormula (answer : Bool) : SetTheorySemisentence 4 :=
  “A n φ b. ∃ F, !sigmaOneMembershipFamilyFormula F ∧
    !boundedPairMemberFormula F n φ ∧ !boundedFunctionFormula b n A ∧
    ∃ U, !sequenceSupportFormula U ∧ A ∈ U ∧ ∃ O ∈ U, !boundedOmegaFormula O ∧
      ∃ T, !membershipTruthTableFormula U O F A T ∧ !(boundedTableAnswerFormula answer) U T n φ b”

theorem sigmaOneMembershipModelTruthFormula_sigmaOne (answer : Bool) :
    IsLevyFormula .sigma 1 (sigmaOneMembershipModelTruthFormula answer) := by
  refine .exs (.and (sigmaOneMembershipFamilyFormula_sigmaOne.subst _) ?_)
  refine .and (.bounded (boundedPairMemberFormula_bounded.subst _))
    (.and (.bounded (boundedFunctionFormula_bounded.subst _)) (.exs ?_))
  refine .and (.bounded (sequenceSupportFormula_bounded.subst _))
    (.and (.bounded (.rel _ _)) (.boundedExs (.bvar 0) ?_))
  exact .and (.bounded (boundedOmegaFormula_bounded.subst _))
    (.exs (.and (.bounded (membershipTruthTableFormula_bounded.subst _))
      (.bounded ((boundedTableAnswerFormula_bounded answer).subst _))))

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem eval_sigmaOneMembershipModelTruthFormula (answer : Bool) (A n φ b : V) :
    (sigmaOneMembershipModelTruthFormula answer).Evalb ![A, n, φ, b] ↔
      IsMembershipFormulaCode n φ ∧ b ∈ A ^ n ∧ TruthAnswer answer (MembershipSatisfies A n φ b) := by
  simp [sigmaOneMembershipModelTruthFormula, Matrix.comp_vecCons', Function.comp_def, Matrix.constant_eq_singleton,
    IsMembershipFormulaCode]
  intro hφ hb
  have hn : n ∈ (ω : V) := IsMembershipFormulaCode.context hφ
  constructor
  · rintro ⟨U, hU, hA, hω, T, hT, hanswer⟩
    let := hU
    have hAU : A ⊆ U := hU.transitive A hA
    have hT' := (eval_membershipTruthTableFormula hAU T).mp hT
    have hanswer' := (eval_boundedTableAnswerFormula answer (IsCodingSupport.natural_mem hn)
      (membershipFormulaCode_formula_mem_support hφ) T b).mp hanswer
    exact (truthAnswer_congr answer (membershipTruthTable_correct hT' hφ hb)).mp hanswer'
  · intro hanswer
    obtain ⟨U, hU, hA⟩ := sequenceSupport_containing A
    let := hU
    have hAU : A ⊆ U := hU.transitive A hA
    refine ⟨U, hU, hA, hU.omega_mem, membershipModelTruthTable A,
      (eval_membershipTruthTableFormula hAU _).mpr (membershipModelTruthTable_correct A), ?_⟩
    apply (eval_boundedTableAnswerFormula answer (IsCodingSupport.natural_mem hn)
      (membershipFormulaCode_formula_mem_support hφ) _ b).mpr
    exact (truthAnswer_congr answer (membershipModelTruthTable_lookup hφ hb)).mpr hanswer

end ZFVP
