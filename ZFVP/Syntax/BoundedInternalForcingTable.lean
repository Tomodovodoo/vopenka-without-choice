import ZFVP.Syntax.BoundedForcingQuantifiers
import ZFVP.Syntax.MembershipTruthTableDefinition

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

def boundedForcingTableAtAssignment : SetTheorySemisentence 11 :=
  “U O F P R D H T n b p. !boundedForcingConstantClause U T n b p ∧
    (∀ r ∈ U, ∀ args ∈ U, !boundedAtomicArgumentsFormula U n r args →
      !boundedForcingAtomicClause U P R H T n b r args p) ∧
    (∀ φ ∈ U, ∀ ψ ∈ U, !boundedPairMemberFormula F n φ → !boundedPairMemberFormula F n ψ →
      !boundedForcingBooleanClause U P R T n b p φ ψ) ∧
    ∀ φ ∈ U, !boundedSuccessorContextFormula U F n φ →
      !boundedForcingQuantifierClause U O P R D T n b p φ”

def boundedInternalForcingTableFormula : SetTheorySemisentence 8 :=
  “U O F P R D H T. ∀ n ∈ O, ∀ b ∈ U, !boundedFunctionFormula b n D →
    ∀ p ∈ P, !boundedForcingTableAtAssignment U O F P R D H T n b p”

theorem boundedForcingTableAtAssignment_bounded : IsBoundedSetFormula boundedForcingTableAtAssignment :=
  .and (boundedForcingConstantClause_bounded.subst _)
    (.and (.all (.bvar 0) (.all (.bvar 1) (.or (boundedAtomicArgumentsFormula_bounded.subst _).neg
      (boundedForcingAtomicClause_bounded.subst _))))
      (.and (.all (.bvar 0) (.all (.bvar 1) (.or (boundedPairMemberFormula_bounded.subst _).neg
        (.or (boundedPairMemberFormula_bounded.subst _).neg (boundedForcingBooleanClause_bounded.subst _)))))
        (.all (.bvar 0) (.or (boundedSuccessorContextFormula_bounded.subst _).neg
          (boundedForcingQuantifierClause_bounded.subst _)))))

theorem boundedInternalForcingTableFormula_bounded : IsBoundedSetFormula boundedInternalForcingTableFormula :=
  .all (.bvar 1) (.all (.bvar 1) (.or (boundedFunctionFormula_bounded.subst _).neg
    (.all (.bvar 5) (boundedForcingTableAtAssignment_bounded.subst _))))

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem eval_boundedForcingTableAtAssignment {U P R D H n b p : V} [IsSequenceSupport U]
    (hP : P ⊆ U) (hD : D ⊆ U) (hH : IsAtomicTruthTable P R U H)
    (hn : n ∈ (ω : V)) (hb : b ∈ D ^ n) (hp : p ∈ P) (T : V) :
    boundedForcingTableAtAssignment.Evalb ![U, ω, formulaFamily membershipLanguageCode ∅, P, R, D, H, T, n, b, p] ↔
      InternalForcingTruthClauses P R D T n b p := by
  have hnU : n ∈ U := IsCodingSupport.natural_mem hn
  have hbU := mem_function_of_mem_function_of_subset hb hD
  have hbmem := function_mem_sequenceSupport hD hn hb
  have hpU := hP p hp
  simp [boundedForcingTableAtAssignment, InternalForcingTruthClauses,
    Matrix.comp_vecCons', Function.comp_def, Matrix.constant_eq_singleton]
  rw [eval_boundedForcingConstantClause hnU hbmem hpU]
  apply and_congr_right
  intro _
  constructor
  · rintro ⟨ha, hbool, hquant⟩
    refine ⟨?_, ?_, ?_⟩
    · intro r args hargs
      obtain ⟨hrU, haU⟩ := membershipAtomicArguments_mem_support (U := U) hn ((membershipAtomicArguments_iff hn).mpr hargs)
      exact (eval_boundedForcingAtomicClause hH hnU hbU hbmem hpU hrU haU T).mp
        (ha r hrU args haU ((eval_boundedAtomicArgumentsFormula hnU r args).mpr hargs))
    · intro φ ψ hφ hψ
      have hφU := membershipFormulaCode_formula_mem_support (U := U) hφ
      have hψU := membershipFormulaCode_formula_mem_support (U := U) hψ
      exact (eval_boundedForcingBooleanClause hP hnU hbmem hpU hφU hψU R T).mp
        (hbool φ hφU ψ hψU hφ hψ)
    · intro φ hφ
      have hφU := membershipFormulaCode_formula_mem_support (U := U) hφ
      exact (eval_boundedForcingQuantifierClause hP hD hn hb hpU hφU R T).mp
        (hquant φ hφU ((eval_boundedSuccessorContextFormula hnU _ φ).mpr hφ))
  · rintro ⟨ha, hbool, hquant⟩
    refine ⟨?_, ?_, ?_⟩
    · intro r hrU args haU hargs
      exact (eval_boundedForcingAtomicClause hH hnU hbU hbmem hpU hrU haU T).mpr
        (ha r args ((eval_boundedAtomicArgumentsFormula hnU r args).mp hargs))
    · intro φ hφU ψ hψU hφ hψ
      exact (eval_boundedForcingBooleanClause hP hnU hbmem hpU hφU hψU R T).mpr (hbool φ ψ hφ hψ)
    · intro φ hφU hφ
      exact (eval_boundedForcingQuantifierClause hP hD hn hb hpU hφU R T).mpr
        (hquant φ ((eval_boundedSuccessorContextFormula hnU _ φ).mp hφ))

theorem eval_boundedInternalForcingTableFormula {U P R D H : V} [IsSequenceSupport U]
    (hP : P ⊆ U) (hD : D ⊆ U) (hH : IsAtomicTruthTable P R U H) (T : V) :
    boundedInternalForcingTableFormula.Evalb ![U, ω, formulaFamily membershipLanguageCode ∅, P, R, D, H, T] ↔
      IsInternalForcingTruthTable P R D T := by
  simp [boundedInternalForcingTableFormula, IsInternalForcingTruthTable,
    Matrix.comp_vecCons', Function.comp_def, Matrix.constant_eq_singleton]
  constructor
  · intro h n hn b hb p hp
    exact (eval_boundedForcingTableAtAssignment hP hD hH hn hb hp T).mp
      (h n hn b (function_mem_sequenceSupport hD hn hb) hb p hp)
  · intro h n hn b _ hb p hp
    exact (eval_boundedForcingTableAtAssignment hP hD hH hn hb hp T).mpr (h n hn b hb p hp)

end ZFVP
