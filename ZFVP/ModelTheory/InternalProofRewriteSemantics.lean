import ZFVP.ModelTheory.InternalProofRewriteAssignments

/-! Semantic equations for the natural-code shift, eigenvariable, and witness operations. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory
open PrimitiveProgram

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem internalSucc_zero : succ (0 : V) = 1 := rfl

theorem satisfies_proofRewrite_shift {M e c : V} (hM : IsStructureCode membershipLanguageCode M)
    (he : e ∈ structureDomain M ^ (ω : V)) (hc : c ∈ (ω : V))
    (hv : requirementFits ((formulaRequirement true).evalSet c) 0) :
    Satisfies membershipLanguageCode ω M e 0
      (decodedNaturalFormula (proofRewriteCode.evalSet (naturalSquarePair 0 (naturalSquarePair 0 c)))) ∅ ↔
      Satisfies membershipLanguageCode ω M (omegaAssignmentShift e) 0 (decodedNaturalFormula c) ∅ := by
  have h0 : (0 : V) ∈ (ω : V) := by simp [zero_def]
  have hb : (∅ : V) ∈ structureDomain M ^ (0 : V) := by simp [mem_function_iff, zero_def]
  have h := satisfies_decodedNaturalFormula_proofRewrite hM h0 hc he hb
    (by simpa only [proofRewriteSource_zeroMode] using hv)
  rw [proofRewriteShift_assignment hM he, proofRewriteBoundTable_zeroMode, graph_empty_compose,
    proofRewriteSource_zeroMode] at h
  exact h

theorem satisfies_proofRewrite_eigen {M e c : V} (hM : IsStructureCode membershipLanguageCode M)
    (he : e ∈ structureDomain M ^ (ω : V)) (hc : c ∈ (ω : V))
    (hv : requirementFits ((formulaRequirement true).evalSet c) 1) :
    Satisfies membershipLanguageCode ω M e 0
      (decodedNaturalFormula (proofRewriteCode.evalSet (naturalSquarePair 1 (naturalSquarePair 0 c)))) ∅ ↔
      Satisfies membershipLanguageCode ω M (omegaAssignmentShift e) 1 (decodedNaturalFormula c)
        (assignmentPrepend 0 ∅ (e ‘ (0 : V))) := by
  have h1 : (1 : V) ∈ (ω : V) := by simp
  have hb : (∅ : V) ∈ structureDomain M ^ (0 : V) := by simp [mem_function_iff, zero_def]
  have hv' : requirementFits ((formulaRequirement true).evalSet c) (proofRewriteSource 1 0) := by
    simpa only [proofRewriteSource_oneMode, internalSucc_zero] using hv
  have h := satisfies_decodedNaturalFormula_proofRewrite hM h1 hc he hb hv'
  rw [proofRewriteEigen_assignment hM he, proofRewriteOpen_assignment hM he h1 one_ne_zero,
    evalSet_proofRewriteFreshIndex_one, proofRewriteSource_oneMode, internalSucc_zero] at h
  exact h

theorem satisfies_proofRewrite_witness {M e c k : V} (hM : IsStructureCode membershipLanguageCode M)
    (he : e ∈ structureDomain M ^ (ω : V)) (hc : c ∈ (ω : V)) (hk : k ∈ (ω : V))
    (hv : requirementFits ((formulaRequirement true).evalSet c) 1) :
    Satisfies membershipLanguageCode ω M e 0
      (decodedNaturalFormula (proofRewriteCode.evalSet (naturalSquarePair (succ (succ k)) (naturalSquarePair 0 c)))) ∅ ↔
      Satisfies membershipLanguageCode ω M e 1 (decodedNaturalFormula c) (assignmentPrepend 0 ∅ (e ‘ k)) := by
  have hs := ω_succ_closed (ω_succ_closed hk)
  have hb : (∅ : V) ∈ structureDomain M ^ (0 : V) := by simp [mem_function_iff, zero_def]
  have hv' : requirementFits ((formulaRequirement true).evalSet c) (proofRewriteSource (succ (succ k)) 0) := by
    simpa only [proofRewriteSource_witnessMode, internalSucc_zero] using hv
  have h := satisfies_decodedNaturalFormula_proofRewrite hM hs hc he hb hv'
  rw [proofRewriteWitness_assignment hM he hk, proofRewriteOpen_assignment hM he hs (internalSucc_ne_zero _),
    evalSet_proofRewriteFreshIndex_witness hk, proofRewriteSource_witnessMode, internalSucc_zero] at h
  exact h

theorem satisfies_proofRewrite_shift_prepend {M e c x : V} (hM : IsStructureCode membershipLanguageCode M)
    (he : e ∈ structureDomain M ^ (ω : V)) (hx : x ∈ structureDomain M) (hc : c ∈ (ω : V))
    (hv : requirementFits ((formulaRequirement true).evalSet c) 0) :
    Satisfies membershipLanguageCode ω M (omegaAssignmentPrepend e x) 0
      (decodedNaturalFormula (proofRewriteCode.evalSet (naturalSquarePair 0 (naturalSquarePair 0 c)))) ∅ ↔
      Satisfies membershipLanguageCode ω M e 0 (decodedNaturalFormula c) ∅ := by
  rw [satisfies_proofRewrite_shift hM (omegaAssignmentPrepend_mem he hx) hc hv,
    omegaAssignmentShift_prepend he hx]

theorem satisfies_proofRewrite_eigen_prepend {M e c x : V} (hM : IsStructureCode membershipLanguageCode M)
    (he : e ∈ structureDomain M ^ (ω : V)) (hx : x ∈ structureDomain M) (hc : c ∈ (ω : V))
    (hv : requirementFits ((formulaRequirement true).evalSet c) 1) :
    Satisfies membershipLanguageCode ω M (omegaAssignmentPrepend e x) 0
      (decodedNaturalFormula (proofRewriteCode.evalSet (naturalSquarePair 1 (naturalSquarePair 0 c)))) ∅ ↔
      Satisfies membershipLanguageCode ω M e 1 (decodedNaturalFormula c) (assignmentPrepend 0 ∅ x) := by
  rw [satisfies_proofRewrite_eigen hM (omegaAssignmentPrepend_mem he hx) hc hv,
    omegaAssignmentShift_prepend he hx, omegaAssignmentPrepend_zero]

end ZFVP
