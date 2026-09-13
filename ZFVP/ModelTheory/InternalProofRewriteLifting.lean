import ZFVP.ModelTheory.InternalProofRewriteStates

/-! The explicit rewrite states are exactly the internally iterated binder lifts. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory
open PrimitiveProgram

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem naturalProofRewriteTerm_bound_lift {s d i : V}
    (hs : s ∈ (ω : V)) (hd : d ∈ (ω : V)) (hi : i ∈ proofRewriteSource s d) :
    naturalProofRewriteTerm s (succ d) (succ (naturalSquarePair 0 (succ i))) =
      (termBoundShift membershipLanguageCode ω d) ‘ (naturalProofRewriteTerm s d (succ (naturalSquarePair 0 i))) := by
  classical
  have hbelow (hi' : i ∈ d) :
      naturalProofRewriteTerm s (succ d) (succ (naturalSquarePair 0 (succ i))) =
        (termBoundShift membershipLanguageCode ω d) ‘ (naturalProofRewriteTerm s d (succ (naturalSquarePair 0 i))) := by
    rw [naturalProofRewriteTerm_bound_below hs (ω_succ_closed hd) (succ_mem_succ_of_natural_mem hd hi'),
      naturalProofRewriteTerm_bound_below hs hd hi', termBoundShift_boundVar membershipLanguageCode_valid hd _ hi']
  by_cases hs0 : s = 0
  · exact hbelow (by simpa only [proofRewriteSource, hs0, ite_true] using hi)
  · have hi' : i ∈ succ d := by simpa only [proofRewriteSource, hs0, ite_false] using hi
    rcases mem_succ_iff.mp hi' with rfl | hi'
    · rw [naturalProofRewriteTerm_bound_edge hs (ω_succ_closed hd) hs0,
        naturalProofRewriteTerm_bound_edge hs hd hs0,
        termBoundShift_freeVar membershipLanguageCode_valid hd _ (evalSet_natural _ hs)]
    · exact hbelow hi'

theorem proofRewriteBoundTable_lift {s d : V} (hs : s ∈ (ω : V)) (hd : d ∈ (ω : V)) :
    proofRewriteBoundTable s (succ d) =
      liftBoundReplacement membershipLanguageCode ω d (proofRewriteSource s d) (proofRewriteBoundTable s d) := by
  have hN := proofRewriteSource_natural s hd
  have hB := proofRewriteBoundTable_mem hs hd
  have hB' := proofRewriteBoundTable_mem hs (ω_succ_closed hd)
  rw [proofRewriteSource_succ] at hB'
  apply function_eq_of_values hB' (liftBoundReplacement_mem membershipLanguageCode_valid hd hN hB)
  intro i hi
  have hi' : i ∈ proofRewriteSource s (succ d) := by simpa only [proofRewriteSource_succ] using hi
  rw [proofRewriteBoundTable_value hi']
  have hiω := IsTransitive.transitive _ (ω_succ_closed hN) _ hi
  rcases internalNatural_cases hiω with rfl | ⟨j, hj, rfl⟩
  · rw [naturalProofRewriteTerm_bound_below hs (ω_succ_closed hd) (zero_mem_succ_natural hd),
      liftBoundReplacement_zero hN]
  · have : IsOrdinal j := IsOrdinal.of_mem hj
    have hne : succ j ≠ (0 : V) := by
      intro he
      exact not_mem_empty (he ▸ mem_succ_self j)
    have hjN : j ∈ proofRewriteSource s d := by
      simpa only [sUnion_succ_of_transitive] using natural_predecessor_mem hN hi hne
    rw [liftBoundReplacement_succ membershipLanguageCode_valid hd hN hB hjN,
      proofRewriteBoundTable_value hjN]
    exact naturalProofRewriteTerm_bound_lift hs hd hjN

theorem proofRewriteFreeTable_lift {s d : V} (hs : s ∈ (ω : V)) (hd : d ∈ (ω : V)) :
    proofRewriteVariableTable s (succ d) 1 =
      liftFreeReplacement membershipLanguageCode ω d (proofRewriteVariableTable s d 1) := by
  have hE := proofRewriteFreeTable_mem hs hd
  apply function_eq_of_values (proofRewriteFreeTable_mem hs (ω_succ_closed hd))
    (liftFreeReplacement_mem membershipLanguageCode_valid hd hE)
  intro i hi
  rw [proofRewriteVariableTable_value _ _ _ hi,
    liftFreeReplacement_value membershipLanguageCode_valid hd hE hi,
    proofRewriteVariableTable_value _ _ _ hi, naturalProofRewriteTerm_free hs (ω_succ_closed hd) hi,
    naturalProofRewriteTerm_free hs hd hi,
    termBoundShift_freeVar membershipLanguageCode_valid hd _ (evalSet_natural _ (naturalSquarePair_natural hs hi))]

theorem proofRewriteState_succ {s d : V} (hs : s ∈ (ω : V)) (hd : d ∈ (ω : V)) :
    proofRewriteState s (succ d) = liftSubstitutionState membershipLanguageCode ω (proofRewriteState s d) := by
  simp only [proofRewriteState, liftSubstitutionState, stateSource_code, stateTarget_code, stateBound_code,
    stateFree_code, proofRewriteSource_succ, proofRewriteBoundTable_lift hs hd, proofRewriteFreeTable_lift hs hd]

theorem substitutionStates_proofRewriteState {s : V} (hs : s ∈ (ω : V)) :
    ∀ d ∈ (ω : V), (substitutionStates membershipLanguageCode ω (proofRewriteState s 0)) ‘ d = proofRewriteState s d := by
  apply naturalNumber_induction (fun d ↦
    (substitutionStates membershipLanguageCode ω (proofRewriteState s 0)) ‘ d = proofRewriteState s d) (by definability)
  · exact substitutionStates_zero _ _ _
  · intro d hd ih
    rw [substitutionStates_succ _ _ _ hd, ih, proofRewriteState_succ hs hd]

end ZFVP
