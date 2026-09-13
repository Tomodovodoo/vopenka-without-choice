import ZFVP.Syntax.BoundedMembershipTruthCertificate
import ZFVP.ModelTheory.OpenCodedSequentSoundness

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

def boundedOpenModelClausesFormula : SetTheorySemisentence 5 :=
  “U C Z F T. ∀ n ∈ U, ∀ φ ∈ U, !boundedPairMemberFormula Z n φ →
    !boundedPairMemberFormula F n φ ∧ ∀ b ∈ U, !boundedFunctionFormula b n C →
      !(boundedTableAnswerFormula true) U T n φ b”

theorem boundedOpenModelClausesFormula_bounded : IsBoundedSetFormula boundedOpenModelClausesFormula :=
  .all (.bvar 0) (.all (.bvar 1) (.or (boundedPairMemberFormula_bounded.subst _).neg
    (.and (boundedPairMemberFormula_bounded.subst _) (.all (.bvar 2)
      (.or (boundedFunctionFormula_bounded.subst _).neg
        ((boundedTableAnswerFormula_bounded true).subst _))))))

def boundedOpenModelCertificate : SetTheorySemisentence 3 :=
  “U C Z. !sequenceSupportFormula U ∧ C ∈ U ∧ Z ∈ U ∧ !boundedNonemptyFormula C ∧
    ∃ F ∈ U, !membershipFamilyWitnessFormula U F ∧ ∃ O ∈ U, !boundedOmegaFormula O ∧
      ∃ T ∈ U, !membershipTruthTableFormula U O F C T ∧ !boundedOpenModelClausesFormula U C Z F T”

theorem boundedOpenModelCertificate_bounded : IsBoundedSetFormula boundedOpenModelCertificate :=
  .and (sequenceSupportFormula_bounded.subst _) (.and (.rel _ _) (.and (.rel _ _)
    (.and (boundedNonemptyFormula_bounded.subst _) (.exs (.bvar 0)
      (.and (membershipFamilyWitnessFormula_bounded.subst _) (.exs (.bvar 1)
        (.and (boundedOmegaFormula_bounded.subst _) (.exs (.bvar 2)
          (.and (membershipTruthTableFormula_bounded.subst _)
            (boundedOpenModelClausesFormula_bounded.subst _))))))))))

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem eval_boundedOpenModelClausesFormula {U C Z T : V} [IsSequenceSupport U]
    (hC : C ∈ U) (hZ : Z ∈ U) (hT : IsMembershipTruthTable C T) (hne : IsNonempty C) :
    boundedOpenModelClausesFormula.Evalb ![U, C, Z, formulaFamily membershipLanguageCode ∅, T] ↔
      SatisfiesOpenCodes C Z := by
  have he : boundedOpenModelClausesFormula.Evalb
      ![U, C, Z, formulaFamily membershipLanguageCode ∅, T] ↔
      ∀ n ∈ U, ∀ φ ∈ U, ⟨n, φ⟩ₖ ∈ Z → IsMembershipFormulaCode n φ ∧
        ∀ b ∈ U, b ∈ C ^ n → ⟨⟨n, φ⟩ₖ, b⟩ₖ ∈ T := by
    simp only [boundedOpenModelClausesFormula]
    simp [Matrix.comp_vecCons', Function.comp_def, Matrix.constant_eq_singleton]
    apply forall_congr'
    intro n
    apply imp_congr_right
    intro hn
    apply forall_congr'
    intro φ
    apply imp_congr_right
    intro hφ
    simp [eval_boundedTableAnswerFormula true hn hφ, TruthAnswer, IsMembershipFormulaCode, TableHolds]
  rw [he]
  constructor
  · intro h
    refine ⟨hne, ?_⟩
    intro n φ hnφ
    have hp : ⟨n, φ⟩ₖ ∈ U := (show IsTransitive U from inferInstance).mem_trans hnφ hZ
    obtain ⟨hn, hφ⟩ := kpair_components_mem_transitive hp
    obtain ⟨hv, hs⟩ := h n hn φ hφ hnφ
    refine ⟨hv, fun b hb ↦ (membershipTruthTable_correct hT hv hb).mp ?_⟩
    exact hs b (function_mem_sequenceSupport
      ((show IsTransitive U from inferInstance).transitive C hC) hv.context hb) hb
  · intro h n _ φ _ hnφ
    obtain ⟨hv, hs⟩ := h.2 n φ hnφ
    exact ⟨hv, fun b _ hb ↦ (membershipTruthTable_correct hT hv hb).mpr (hs b hb)⟩

theorem eval_boundedOpenModelCertificate (U C Z : V) :
    boundedOpenModelCertificate.Evalb ![U, C, Z] ↔
      IsSequenceSupport U ∧ C ∈ U ∧ Z ∈ U ∧ IsNonempty C ∧
      (formulaFamily membershipLanguageCode ∅ : V) ∈ U ∧
      identity (formulaFamily membershipLanguageCode ∅ : V) ∈ U ∧
      ∃ T ∈ U, IsMembershipTruthTable C T ∧ SatisfiesOpenCodes C Z := by
  simp only [boundedOpenModelCertificate]
  simp [Matrix.comp_vecCons', Function.comp_def, Matrix.constant_eq_singleton,
    eval_membershipFamilyWitnessFormula]
  intro hU
  let := hU
  intro hC hZ hne
  rw [and_iff_right (show IsCodingSupport U from inferInstance)]
  simp only [and_assoc]
  intro hF
  rw [and_iff_right hF]
  apply and_congr_right
  intro _
  rw [and_iff_right hU.omega_mem]
  apply exists_congr
  intro T
  apply and_congr_right
  intro _
  rw [eval_membershipTruthTableFormula (hU.transitive C hC)]
  apply and_congr_right
  intro hT
  exact eval_boundedOpenModelClausesFormula hC hZ hT hne

theorem boundedOpenModelCertificate_exists (C Z : V) :
    (∃ U : V, boundedOpenModelCertificate.Evalb ![U, C, Z]) ↔ SatisfiesOpenCodes C Z := by
  simp only [eval_boundedOpenModelCertificate]
  constructor
  · rintro ⟨_, _, _, _, _, _, _, _, _, _, h⟩
    exact h
  · intro h
    let F := (formulaFamily membershipLanguageCode ∅ : V)
    let T := membershipModelTruthTable C
    obtain ⟨U, hU, hp⟩ := sequenceSupport_containing ⟨⟨C, Z⟩ₖ, ⟨F, ⟨identity F, T⟩ₖ⟩ₖ⟩ₖ
    let := hU
    obtain ⟨hpCZ, hp⟩ := kpair_components_mem_transitive hp
    obtain ⟨hC, hZ⟩ := kpair_components_mem_transitive hpCZ
    obtain ⟨hF, hp⟩ := kpair_components_mem_transitive hp
    obtain ⟨hs, hT⟩ := kpair_components_mem_transitive hp
    exact ⟨U, hU, hC, hZ, h.1, hF, hs, T, hT, membershipModelTruthTable_correct C, h⟩

def sigmaOneOpenModelFormula : SetTheorySemisentence 2 := .exs boundedOpenModelCertificate

theorem sigmaOneOpenModelFormula_sigmaOne : IsSigmaFormula 1 sigmaOneOpenModelFormula :=
  .exs (.bounded boundedOpenModelCertificate_bounded)

theorem eval_sigmaOneOpenModelFormula (C Z : V) :
    sigmaOneOpenModelFormula.Evalb ![C, Z] ↔ SatisfiesOpenCodes C Z :=
  boundedOpenModelCertificate_exists C Z

end ZFVP
