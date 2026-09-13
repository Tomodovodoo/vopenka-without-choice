import ZFVP.Syntax.BoundedPreviousCodes
import ZFVP.Syntax.BoundedCertificates

/-! Bounded constructor checks for individual derivation steps. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def boundedAtomicCaseFormula : SetTheorySemisentence 3 :=
  “U n φ. ∃ r ∈ U, ∃ args ∈ U, !boundedAtomicArgumentsFormula U n r args ∧
    (!(CodeExpression.atom (.var 0) (.var 1)).formula U φ r args ∨
      !(CodeExpression.negAtom (.var 0) (.var 1)).formula U φ r args)”

def boundedBooleanCaseFormula : SetTheorySemisentence 5 :=
  “U s i n φ. ∃ ψ ∈ U, ∃ χ ∈ U,
    !boundedPreviousCodeFormula U s i n ψ ∧ !boundedPreviousCodeFormula U s i n χ ∧
    (!(CodeExpression.conj (.var 0) (.var 1)).formula U φ ψ χ ∨
      !(CodeExpression.disj (.var 0) (.var 1)).formula U φ ψ χ)”

def boundedShiftedPreviousFormula : SetTheorySemisentence 5 :=
  “U s i n φ. ∃ m ∈ U, !boundedSuccFormula m n ∧ !boundedPreviousCodeFormula U s i m φ”

def boundedQuantifierCaseFormula : SetTheorySemisentence 5 :=
  “U s i n φ. ∃ j ∈ n, ∃ ψ ∈ U, !boundedShiftedPreviousFormula U s i n ψ ∧
    (!(CodeExpression.boundedAll (.var 0) (.var 1)).formula U φ j ψ ∨
      !(CodeExpression.boundedExs (.var 0) (.var 1)).formula U φ j ψ)”

theorem boundedAtomicCaseFormula_bounded : IsBoundedSetFormula boundedAtomicCaseFormula :=
  .exs (.bvar 0) (.exs (.bvar 1) (.and (boundedAtomicArgumentsFormula_bounded.subst _)
    (.or ((CodeExpression.atom (.var 0) (.var 1)).formula_bounded.subst _)
      ((CodeExpression.negAtom (.var 0) (.var 1)).formula_bounded.subst _))))

theorem boundedBooleanCaseFormula_bounded : IsBoundedSetFormula boundedBooleanCaseFormula :=
  .exs (.bvar 0) (.exs (.bvar 1) (.and (boundedPreviousCodeFormula_bounded.subst _)
    (.and (boundedPreviousCodeFormula_bounded.subst _)
      (.or ((CodeExpression.conj (.var 0) (.var 1)).formula_bounded.subst _)
        ((CodeExpression.disj (.var 0) (.var 1)).formula_bounded.subst _)))))

theorem boundedShiftedPreviousFormula_bounded : IsBoundedSetFormula boundedShiftedPreviousFormula :=
  .exs (.bvar 0) (.and (boundedSuccFormula_bounded.subst _) (boundedPreviousCodeFormula_bounded.subst _))

theorem boundedQuantifierCaseFormula_bounded : IsBoundedSetFormula boundedQuantifierCaseFormula :=
  .exs (.bvar 3) (.exs (.bvar 1) (.and (boundedShiftedPreviousFormula_bounded.subst _)
    (.or ((CodeExpression.boundedAll (.var 0) (.var 1)).formula_bounded.subst _)
      ((CodeExpression.boundedExs (.var 0) (.var 1)).formula_bounded.subst _))))

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem eval_boundedAtomicCaseFormula {U n : V} [IsCodingSupport U] (hn : n ∈ U) (φ : V) :
    boundedAtomicCaseFormula.Evalb ![U, n, φ] ↔
      ∃ r ∈ U, ∃ args ∈ U, IsMembershipAtomicArguments n r args ∧
        (φ = atomCode r args ∨ φ = negAtomCode r args) := by
  simp only [boundedAtomicCaseFormula]
  simp [Matrix.comp_vecCons', Function.comp_def, Matrix.constant_eq_singleton]
  refine exists_congr fun r ↦ and_congr_right fun hr ↦ exists_congr fun args ↦ and_congr_right fun ha ↦ ?_
  rw [eval_boundedAtomicArgumentsFormula hn,
    CodeExpression.eval_formula_two _ _ _ _ _ hr ha,
    CodeExpression.eval_formula_two _ _ _ _ _ hr ha]
  simp [CodeExpression.eval]

theorem eval_boundedBooleanCaseFormula {U n : V} [IsCodingSupport U] (hn : n ∈ U) (s i φ : V) :
    boundedBooleanCaseFormula.Evalb ![U, s, i, n, φ] ↔
      ∃ ψ ∈ U, ∃ χ ∈ U, ⟨n, ψ⟩ₖ ∈ range (s ↾ i) ∧ ⟨n, χ⟩ₖ ∈ range (s ↾ i) ∧
        (φ = andCode ψ χ ∨ φ = orCode ψ χ) := by
  simp only [boundedBooleanCaseFormula]
  simp [Matrix.comp_vecCons', Function.comp_def, Matrix.constant_eq_singleton]
  refine exists_congr fun ψ ↦ and_congr_right fun hψ ↦ exists_congr fun χ ↦ and_congr_right fun hχ ↦ ?_
  rw [eval_boundedPreviousCodeFormula _ _ hn hψ, eval_boundedPreviousCodeFormula _ _ hn hχ,
    CodeExpression.eval_formula_two _ _ _ _ _ hψ hχ,
    CodeExpression.eval_formula_two _ _ _ _ _ hψ hχ]
  simp [CodeExpression.eval]

theorem eval_boundedShiftedPreviousFormula {U n φ : V} [hU : IsCodingSupport U]
    (hn : n ∈ U) (hφ : φ ∈ U) (s i : V) :
    boundedShiftedPreviousFormula.Evalb ![U, s, i, n, φ] ↔ ⟨succ n, φ⟩ₖ ∈ range (s ↾ i) := by
  simp [boundedShiftedPreviousFormula, Matrix.comp_vecCons', Function.comp_def, Matrix.constant_eq_singleton]
  exact and_iff_right (hU.succ_closed n hn) |>.trans
    (eval_boundedPreviousCodeFormula s i (hU.succ_closed n hn) hφ)

theorem eval_boundedQuantifierCaseFormula {U n : V} [hU : IsCodingSupport U] (hn : n ∈ U) (s i φ : V) :
    boundedQuantifierCaseFormula.Evalb ![U, s, i, n, φ] ↔
      ∃ j ∈ n, ∃ ψ ∈ U, ⟨succ n, ψ⟩ₖ ∈ range (s ↾ i) ∧
        (φ = boundedAllCode j ψ ∨ φ = boundedExistsCode j ψ) := by
  simp only [boundedQuantifierCaseFormula]
  simp [Matrix.comp_vecCons', Function.comp_def, Matrix.constant_eq_singleton]
  refine exists_congr fun j ↦ and_congr_right fun hj ↦ exists_congr fun ψ ↦ and_congr_right fun hψ ↦ ?_
  rw [eval_boundedShiftedPreviousFormula hn hψ,
    CodeExpression.eval_formula_two _ _ _ _ _ (hU.mem_trans hj hn) hψ,
    CodeExpression.eval_formula_two _ _ _ _ _ (hU.mem_trans hj hn) hψ]
  simp [CodeExpression.eval]

theorem binaryCode_parameters_mem {U t a b : V} [IsTransitive U]
    (h : ⟨t, ⟨a, b⟩ₖ⟩ₖ ∈ U) : a ∈ U ∧ b ∈ U :=
  kpair_components_mem_transitive (kpair_components_mem_transitive h).2

theorem boundedAtomicCase_iff {U n φ : V} [IsCodingSupport U] (hn : n ∈ U) (hφ : φ ∈ U) :
    boundedAtomicCaseFormula.Evalb ![U, n, φ] ↔
      ∃ r args, IsMembershipAtomicArguments n r args ∧ (φ = atomCode r args ∨ φ = negAtomCode r args) := by
  rw [eval_boundedAtomicCaseFormula hn]
  constructor
  · rintro ⟨r, _, args, _, ha, h⟩
    exact ⟨r, args, ha, h⟩
  · rintro ⟨r, args, ha, h⟩
    have hm : r ∈ U ∧ args ∈ U := by
      rcases h with h | h
      · exact binaryCode_parameters_mem (h ▸ hφ)
      · exact binaryCode_parameters_mem (h ▸ hφ)
    exact ⟨r, hm.1, args, hm.2, ha, h⟩

theorem boundedBooleanCase_iff {U n s : V} [IsCodingSupport U] (hn : n ∈ U) (hs : s ∈ U) (i φ : V) :
    boundedBooleanCaseFormula.Evalb ![U, s, i, n, φ] ↔
      ∃ ψ χ, ⟨n, ψ⟩ₖ ∈ range (s ↾ i) ∧ ⟨n, χ⟩ₖ ∈ range (s ↾ i) ∧
        (φ = andCode ψ χ ∨ φ = orCode ψ χ) := by
  rw [eval_boundedBooleanCaseFormula hn]
  constructor
  · rintro ⟨ψ, _, χ, _, hψ, hχ, h⟩
    exact ⟨ψ, χ, hψ, hχ, h⟩
  · rintro ⟨ψ, χ, hψ, hχ, h⟩
    exact ⟨ψ, (previousCode_components_mem hs hψ).2, χ, (previousCode_components_mem hs hχ).2, hψ, hχ, h⟩

theorem boundedQuantifierCase_iff {U n s : V} [IsCodingSupport U] (hn : n ∈ U) (hs : s ∈ U) (i φ : V) :
    boundedQuantifierCaseFormula.Evalb ![U, s, i, n, φ] ↔
      ∃ j ∈ n, ∃ ψ, ⟨succ n, ψ⟩ₖ ∈ range (s ↾ i) ∧
        (φ = boundedAllCode j ψ ∨ φ = boundedExistsCode j ψ) := by
  rw [eval_boundedQuantifierCaseFormula hn]
  constructor
  · rintro ⟨j, hj, ψ, _, hψ, h⟩
    exact ⟨j, hj, ψ, hψ, h⟩
  · rintro ⟨j, hj, ψ, hψ, h⟩
    exact ⟨j, hj, ψ, (previousCode_components_mem hs hψ).2, hψ, h⟩

end ZFVP
