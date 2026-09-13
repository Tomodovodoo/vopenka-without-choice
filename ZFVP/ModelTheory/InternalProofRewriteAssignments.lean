import ZFVP.ModelTheory.InternalProofRewriteModes
import ZFVP.Syntax.OmegaAssignments
import ZFVP.SetTheory.CompositionLaws

/-! The assignments induced by the proof-rule rewrite tables. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory
open PrimitiveProgram

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem proofRewriteShift_assignment {M e : V} (hM : IsStructureCode membershipLanguageCode M)
    (he : e ∈ structureDomain M ^ (ω : V)) :
    compose (proofRewriteVariableTable 0 0 1) (termEvaluation membershipLanguageCode ω 0 M ∅ e) =
      omegaAssignmentShift e := by
  have h0 : (0 : V) ∈ (ω : V) := by simp [zero_def]
  have hb : (∅ : V) ∈ structureDomain M ^ (0 : V) := by simp [mem_function_iff, zero_def]
  have hE := proofRewriteFreeTable_mem h0 h0
  have hT := termEvaluation_mem_function hM h0 ω hb he
  apply function_eq_of_values (compose_function hE hT) (omegaAssignmentShift_mem he)
  intro i hi
  rw [value_compose_of_mem_function hE hT hi, proofRewriteFreeTable_zeroMode_value hi,
    termEvaluation_freeVar hM.language h0 _ _ _ _ (ω_succ_closed hi), omegaAssignmentShift_value _ hi]

theorem proofRewriteEigen_assignment {M e : V} (hM : IsStructureCode membershipLanguageCode M)
    (he : e ∈ structureDomain M ^ (ω : V)) :
    compose (proofRewriteVariableTable 1 0 1) (termEvaluation membershipLanguageCode ω 0 M ∅ e) =
      omegaAssignmentShift e := by
  rw [proofRewriteFreeTable_eigen_eq_shift, proofRewriteShift_assignment hM he]

theorem proofRewriteWitness_assignment {M e k : V} (hM : IsStructureCode membershipLanguageCode M)
    (he : e ∈ structureDomain M ^ (ω : V)) (hk : k ∈ (ω : V)) :
    compose (proofRewriteVariableTable (succ (succ k)) 0 1) (termEvaluation membershipLanguageCode ω 0 M ∅ e) = e := by
  have h0 : (0 : V) ∈ (ω : V) := by simp [zero_def]
  have hb : (∅ : V) ∈ structureDomain M ^ (0 : V) := by simp [mem_function_iff, zero_def]
  have hE := proofRewriteFreeTable_mem (ω_succ_closed (ω_succ_closed hk)) h0
  have hT := termEvaluation_mem_function hM h0 ω hb he
  apply function_eq_of_values (compose_function hE hT) he
  intro i hi
  rw [value_compose_of_mem_function hE hT hi, proofRewriteFreeTable_witnessMode_value hk hi,
    termEvaluation_freeVar hM.language h0 _ _ _ _ hi]

theorem proofRewriteOpen_assignment {M e s : V} (hM : IsStructureCode membershipLanguageCode M)
    (he : e ∈ structureDomain M ^ (ω : V)) (hs : s ∈ (ω : V)) (hs0 : s ≠ 0) :
    compose (proofRewriteBoundTable s 0) (termEvaluation membershipLanguageCode ω 0 M ∅ e) =
      assignmentPrepend 0 ∅ (e ‘ (proofRewriteFreshIndex.evalSet s)) := by
  have h0 : (0 : V) ∈ (ω : V) := by simp [zero_def]
  have hb : (∅ : V) ∈ structureDomain M ^ (0 : V) := by simp [mem_function_iff, zero_def]
  have hB : proofRewriteBoundTable s 0 ∈ termSet (membershipLanguageCode : V) ω 0 ^ succ (0 : V) := by
    simpa only [proofRewriteSource, hs0, ite_false] using proofRewriteBoundTable_mem hs h0
  have hT := termEvaluation_mem_function hM h0 ω hb he
  apply function_eq_of_values (compose_function hB hT)
    (assignmentPrepend_mem_function h0 hb (function_value_mem he (evalSet_natural _ hs)))
  intro i hi
  have hi0 : i = (0 : V) := by simpa [mem_succ_iff, zero_def] using hi
  subst i
  rw [value_compose_of_mem_function hB hT hi, proofRewriteBoundTable_open_value hs hs0,
    termEvaluation_freeVar hM.language h0 _ _ _ _ (evalSet_natural _ hs), assignmentPrepend_zero h0]

end ZFVP
