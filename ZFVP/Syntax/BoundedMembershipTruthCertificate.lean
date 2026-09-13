import ZFVP.Syntax.DeltaOneMembershipTruth

/-! A single set contains every witness needed to check set-domain truth boundedly. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def boundedMembershipTruthCertificate (answer : Bool) : SetTheorySemisentence 5 :=
  “U A n φ b. !sequenceSupportFormula U ∧ A ∈ U ∧
    ∃ F ∈ U, !membershipFamilyWitnessFormula U F ∧
      !boundedPairMemberFormula F n φ ∧ !boundedFunctionFormula b n A ∧
      ∃ O ∈ U, !boundedOmegaFormula O ∧ ∃ T ∈ U,
        !membershipTruthTableFormula U O F A T ∧ !(boundedTableAnswerFormula answer) U T n φ b”

theorem boundedMembershipTruthCertificate_bounded (answer : Bool) :
    IsBoundedSetFormula (boundedMembershipTruthCertificate answer) :=
  .and (sequenceSupportFormula_bounded.subst _) (.and (.rel _ _)
    (.exs (.bvar 0) (.and (membershipFamilyWitnessFormula_bounded.subst _)
      (.and (boundedPairMemberFormula_bounded.subst _)
        (.and (boundedFunctionFormula_bounded.subst _) (.exs (.bvar 1)
          (.and (boundedOmegaFormula_bounded.subst _) (.exs (.bvar 2)
            (.and (membershipTruthTableFormula_bounded.subst _)
              ((boundedTableAnswerFormula_bounded answer).subst _))))))))))

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem eval_membershipFamilyWitnessFormula (U F : V) :
    membershipFamilyWitnessFormula.Evalb ![U, F] ↔
      IsCodingSupport U ∧ F ∈ U ∧ identity F ∈ U ∧
        F = (formulaFamily membershipLanguageCode ∅ : V) := by
  simp [membershipFamilyWitnessFormula, Matrix.comp_vecCons', Function.comp_def,
    Matrix.constant_eq_singleton]
  intro hU
  let := hU
  intro hF
  rw [and_iff_right hU.omega_mem]
  exact and_congr_right fun hs ↦ eval_membershipFixedPointFormula hF hs

theorem eval_boundedMembershipTruthCertificate (answer : Bool) (U A n φ b : V) :
    (boundedMembershipTruthCertificate answer).Evalb ![U, A, n, φ, b] ↔
      IsSequenceSupport U ∧ A ∈ U ∧
      (formulaFamily membershipLanguageCode ∅ : V) ∈ U ∧
      identity (formulaFamily membershipLanguageCode ∅ : V) ∈ U ∧
      IsMembershipFormulaCode n φ ∧ b ∈ A ^ n ∧
      ∃ T ∈ U, IsMembershipTruthTable A T ∧
        TruthAnswer answer (⟨⟨n, φ⟩ₖ, b⟩ₖ ∈ T) := by
  simp only [boundedMembershipTruthCertificate]
  simp [Matrix.comp_vecCons', Function.comp_def, Matrix.constant_eq_singleton,
    eval_membershipFamilyWitnessFormula]
  intro hU
  let := hU
  intro hA
  rw [and_iff_right (show IsCodingSupport U from inferInstance)]
  simp only [and_assoc]
  intro hF
  rw [and_iff_right hF]
  apply and_congr_right
  intro hs
  apply and_congr_right
  intro hφ
  apply and_congr_right
  intro hb
  rw [and_iff_right hU.omega_mem]
  apply exists_congr
  intro T
  apply and_congr_right
  intro _
  rw [eval_membershipTruthTableFormula (hU.transitive A hA)]
  apply and_congr_right
  intro _
  exact eval_boundedTableAnswerFormula answer
    (IsCodingSupport.natural_mem (IsMembershipFormulaCode.context hφ))
    (membershipFormulaCode_formula_mem_support hφ) T b

theorem boundedMembershipTruthCertificate_exists (answer : Bool) (A n φ b : V) :
    (∃ U : V, (boundedMembershipTruthCertificate answer).Evalb ![U, A, n, φ, b]) ↔
      IsMembershipFormulaCode n φ ∧ b ∈ A ^ n ∧
        TruthAnswer answer (MembershipSatisfies A n φ b) := by
  simp only [eval_boundedMembershipTruthCertificate]
  constructor
  · rintro ⟨U, _, _, _, _, hφ, hb, T, _, hT, ht⟩
    exact ⟨hφ, hb, (truthAnswer_congr answer (membershipTruthTable_correct hT hφ hb)).mp ht⟩
  · rintro ⟨hφ, hb, ht⟩
    let F := (formulaFamily membershipLanguageCode ∅ : V)
    let T := membershipModelTruthTable A
    obtain ⟨U, hU, hp⟩ := sequenceSupport_containing ⟨A, ⟨F, ⟨identity F, T⟩ₖ⟩ₖ⟩ₖ
    let := hU
    obtain ⟨hA, hp⟩ := kpair_components_mem_transitive hp
    obtain ⟨hF, hp⟩ := kpair_components_mem_transitive hp
    obtain ⟨hs, hT⟩ := kpair_components_mem_transitive hp
    exact ⟨U, hU, hA, hF, hs, hφ, hb, T, hT, membershipModelTruthTable_correct A,
      (truthAnswer_congr answer (membershipModelTruthTable_lookup hφ hb)).mpr ht⟩

end ZFVP
