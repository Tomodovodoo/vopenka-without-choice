import ZFVP.SetTheory.BoundedSequenceSupport
import ZFVP.Syntax.Assignments
import ZFVP.SetTheory.FunctionUnion

/-! A bounded relational check for prepending to an internal finite assignment. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def boundedAssignmentPrependFormula : SetTheorySemisentence 6 :=
  “U O f n b x. ∃ m ∈ O, !boundedSuccFormula m n ∧ !boundedFunctionFormula f m U ∧
    (∃ z ∈ m, !boundedEmptyFormula z ∧ !boundedPairMemberFormula f z x) ∧
    ∀ i ∈ n, ∃ j ∈ m, !boundedSuccFormula j i ∧ ∃ y ∈ U,
      !boundedPairMemberFormula b i y ∧ !boundedPairMemberFormula f j y”

theorem boundedAssignmentPrependFormula_bounded : IsBoundedSetFormula boundedAssignmentPrependFormula :=
  .exs (.bvar 1) (.and (boundedSuccFormula_bounded.subst _) (.and (boundedFunctionFormula_bounded.subst _)
    (.and (.exs (.bvar 0) (.and (boundedEmptyFormula_bounded.subst _) (boundedPairMemberFormula_bounded.subst _)))
      (.all (.bvar 4) (.exs (.bvar 1) (.and (boundedSuccFormula_bounded.subst _)
        (.exs (.bvar 3) (.and (boundedPairMemberFormula_bounded.subst _) (boundedPairMemberFormula_bounded.subst _)))))))))

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem assignmentPrepend_eq_of_pairs {U f n b x : V} (hn : n ∈ (ω : V))
    (hf : f ∈ U ^ succ n) (hzero : ⟨(0 : V), x⟩ₖ ∈ f)
    (hsucc : ∀ i ∈ n, ⟨succ i, b ‘ i⟩ₖ ∈ f) : f = assignmentPrepend n b x := by
  have : IsFunction f := IsFunction.of_mem hf
  apply functions_eq_of_domain_values (by simp [domain_eq_of_mem_function hf])
  intro j hj
  rw [domain_eq_of_mem_function hf] at hj
  have hjω : j ∈ (ω : V) := IsOrdinal.toIsTransitive.mem_trans hj (ω_succ_closed hn)
  rcases internalNatural_cases hjω with rfl | ⟨i, hiω, rfl⟩
  · rw [value_eq_of_kpair_mem hzero, assignmentPrepend_zero hn]
  · have : IsOrdinal i := IsOrdinal.of_mem hiω
    have hne : succ i ≠ (0 : V) := by
      intro h
      exact not_mem_empty (h ▸ (show i ∈ succ i by simp))
    have hi : i ∈ n := by
      simpa only [sUnion_succ_of_transitive] using natural_predecessor_mem hn hj hne
    rw [value_eq_of_kpair_mem (hsucc i hi), assignmentPrepend_succ hn hi]

theorem eval_boundedAssignmentPrependFormula {U n b x : V} (hn : n ∈ (ω : V))
    (hb : b ∈ U ^ n) (hx : x ∈ U) (f : V) :
    boundedAssignmentPrependFormula.Evalb ![U, ω, f, n, b, x] ↔ f = assignmentPrepend n b x := by
  have : IsFunction b := IsFunction.of_mem hb
  simp [boundedAssignmentPrependFormula, Matrix.comp_vecCons', Function.comp_def, Matrix.constant_eq_singleton,
    ω_succ_closed hn]
  constructor
  · rintro ⟨hf, hzero, hs⟩
    apply assignmentPrepend_eq_of_pairs hn hf hzero.2
    intro i hi
    obtain ⟨_, y, _, hbiy, hfiy⟩ := hs i hi
    rwa [← value_eq_of_kpair_mem hbiy] at hfiy
  · rintro rfl
    have hf := assignmentPrepend_mem_function hn hb hx
    have hz : ⟨(0 : V), x⟩ₖ ∈ assignmentPrepend n b x :=
      kpair_mem_iff_value.mpr ⟨by simpa using zero_mem_succ_natural hn, assignmentPrepend_zero hn b x⟩
    refine ⟨hf, ⟨zero_mem_succ_natural hn, hz⟩, ?_⟩
    intro i hi
    refine ⟨succ_mem_succ_of_natural_mem hn hi, b ‘ i, function_value_mem hb hi,
      kpair_value_mem (domain_eq_of_mem_function hb ▸ hi), ?_⟩
    exact kpair_mem_iff_value.mpr ⟨by simpa using succ_mem_succ_of_natural_mem hn hi,
      assignmentPrepend_succ hn hi b x⟩

end ZFVP
