import ZFVP.ModelTheory.InternalReindexStates

/-! Finite renaming tables are the iterated capture-avoiding binder lifts. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory
open PrimitiveProgram

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem finiteReindexBoundTable_lift {r m d : V}
    (hr : r ∈ (ω : V)) (hm : m ∈ (ω : V)) (hd : d ∈ (ω : V))
    (hR : ∀ j ∈ listLength.evalSet r, listGet.evalSet (naturalSquarePair r j) ∈ m) :
    finiteReindexBoundTable r (succ d) =
      liftBoundReplacement membershipLanguageCode ∅ (ordinalAdd m d) (reindexSource r d)
        (finiteReindexBoundTable r d) := by
  have : IsOrdinal m := IsOrdinal.of_mem hm
  have : IsOrdinal d := IsOrdinal.of_mem hd
  have hN := reindexSource_natural hr hd
  have hM := ordinalAdd_natural hm hd
  have hB := finiteReindexBoundTable_mem hr hm hd hR
  have hB' := finiteReindexBoundTable_mem hr hm (ω_succ_closed hd) hR
  rw [reindexSource_succ hr hd, ordinalAdd_succ] at hB'
  apply function_eq_of_values hB' (liftBoundReplacement_mem membershipLanguageCode_valid hM hN hB)
  intro i hi
  have hi' : i ∈ reindexSource r (succ d) := by simpa only [reindexSource_succ hr hd] using hi
  rw [finiteReindexBoundTable_value hi']
  have hiω := IsTransitive.transitive _ (ω_succ_closed hN) _ hi
  rcases internalNatural_cases hiω with rfl | ⟨j, hj, rfl⟩
  · rw [naturalReindexVariable_lift_zero hr hd, liftBoundReplacement_zero hN]
  · have : IsOrdinal j := IsOrdinal.of_mem hj
    have hne : succ j ≠ (0 : V) := by
      intro he
      exact not_mem_empty (he ▸ mem_succ_self j)
    have hjN : j ∈ reindexSource r d := by
      simpa only [sUnion_succ_of_transitive] using natural_predecessor_mem hN hi hne
    rw [liftBoundReplacement_succ membershipLanguageCode_valid hM hN hB hjN,
      finiteReindexBoundTable_value hjN, naturalReindexVariable_lift_succ hr hd hj,
      termBoundShift_boundVar membershipLanguageCode_valid hM ∅ (naturalReindexVariable_bound hr hm hd hR hjN)]

theorem reindexState_succ {r m d : V}
    (hr : r ∈ (ω : V)) (hm : m ∈ (ω : V)) (hd : d ∈ (ω : V))
    (hR : ∀ j ∈ listLength.evalSet r, listGet.evalSet (naturalSquarePair r j) ∈ m) :
    reindexState r m (succ d) = liftSubstitutionState membershipLanguageCode ∅ (reindexState r m d) := by
  have : IsOrdinal m := IsOrdinal.of_mem hm
  have : IsOrdinal d := IsOrdinal.of_mem hd
  simp only [reindexState, liftSubstitutionState, stateSource_code, stateTarget_code, stateBound_code,
    stateFree_code, reindexSource_succ hr hd, ordinalAdd_succ, finiteReindexBoundTable_lift hr hm hd hR,
    liftFreeReplacement, graph_empty_compose]

theorem substitutionStates_reindexState {r m : V}
    (hr : r ∈ (ω : V)) (hm : m ∈ (ω : V))
    (hR : ∀ j ∈ listLength.evalSet r, listGet.evalSet (naturalSquarePair r j) ∈ m) :
    ∀ d ∈ (ω : V), (substitutionStates membershipLanguageCode ∅ (reindexState r m 0)) ‘ d = reindexState r m d := by
  apply naturalNumber_induction (fun d ↦
    (substitutionStates membershipLanguageCode ∅ (reindexState r m 0)) ‘ d = reindexState r m d) (by definability)
  · exact substitutionStates_zero _ _ _
  · intro d hd ih
    rw [substitutionStates_succ _ _ _ hd, ih, reindexState_succ hr hm hd hR]

theorem finiteReindexBoundTable_zero {r m : V}
    (hr : r ∈ (ω : V)) (hm : m ∈ (ω : V))
    (hR : decodedNaturalList r ∈ m ^ listLength.evalSet r) :
    finiteReindexBoundTable r 0 = compose (decodedNaturalList r) (boundVariableAssignment m) := by
  have hB : finiteReindexBoundTable r 0 ∈ termSet membershipLanguageCode ∅ m ^ listLength.evalSet r := by
    unfold finiteReindexBoundTable
    rw [reindexSource_zero]
    apply definableGraph_mem_function_of_mapsTo
    intro i hi
    rw [naturalReindexVariable_zeroDepth hr hi, ← value_decodedNaturalList hi]
    exact (termSet_closed membershipLanguageCode_valid hm ∅).1 _ (function_value_mem hR hi)
  apply function_eq_of_values hB (compose_function hR (boundVariableAssignment_mem hm))
  intro i hi
  rw [finiteReindexBoundTable_value (r := r) (d := 0) (by simpa only [reindexSource_zero] using hi),
    naturalReindexVariable_zeroDepth hr hi, value_compose_of_mem_function hR (boundVariableAssignment_mem hm) hi,
    boundVariableAssignment_value (function_value_mem hR hi), value_decodedNaturalList hi]

theorem reindexState_zero {r m : V}
    (hr : r ∈ (ω : V)) (hm : m ∈ (ω : V))
    (hR : decodedNaturalList r ∈ m ^ listLength.evalSet r) :
    reindexState r m 0 = substitutionState (listLength.evalSet r) m
      (compose (decodedNaturalList r) (boundVariableAssignment m)) ∅ := by
  rw [reindexState, reindexSource_zero, finiteReindexBoundTable_zero hr hm hR]
  simp only [zero_def, ordinalAdd_zero]

end ZFVP
