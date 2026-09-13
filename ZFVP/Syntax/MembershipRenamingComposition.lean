import ZFVP.Syntax.MembershipSubstitutionComposition

/-! Identity and composition for every internally finite membership formula. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem renameMembershipFormula_compose {n m l r s φ : V}
    (hn : n ∈ (ω : V)) (hm : m ∈ (ω : V)) (hl : l ∈ (ω : V))
    (hr : r ∈ m ^ n) (hs : s ∈ l ^ m)
    (hφ : φ ∈ formulaSet membershipLanguageCode ∅ n) :
    renameMembershipFormula m l s (renameMembershipFormula n m r φ) =
      renameMembershipFormula n l (compose r s) φ := by
  let a := substitutionState n m (compose r (boundVariableAssignment m)) (∅ : V)
  let b := substitutionState m l (compose s (boundVariableAssignment l)) (∅ : V)
  let c := substitutionState n l (compose (compose r s) (boundVariableAssignment l)) (∅ : V)
  have ha : IsSubstitutionState membershipLanguageCode ∅ ∅ a := membershipRenaming_state hn hm hr
  have hb : IsSubstitutionState membershipLanguageCode ∅ ∅ b := membershipRenaming_state hm hl hs
  have hc : IsSubstitutionState membershipLanguageCode ∅ ∅ c := membershipRenaming_state hn hl (compose_function hr hs)
  have hab : IsMembershipStateComposition a b c := by
    simp only [IsMembershipStateComposition, a, b, c, stateSource_code, stateTarget_code, stateBound_code,
      true_and]
    intro i hi
    simp only [membershipStateTermMap, stateSource_code, stateBound_code, stateFree_code]
    rw [value_compose_of_mem_function hr (boundVariableAssignment_mem hm) hi,
      boundVariableAssignment_value (function_value_mem hr hi),
      termSubstitution_boundVar membershipLanguageCode_valid hm _ _ _ (function_value_mem hr hi),
      value_compose_of_mem_function hs (boundVariableAssignment_mem hl) (function_value_mem hr hi),
      boundVariableAssignment_value (function_value_mem hs (function_value_mem hr hi)),
      value_compose_of_mem_function (compose_function hr hs) (boundVariableAssignment_mem hl) hi,
      boundVariableAssignment_value (function_value_mem (compose_function hr hs) hi),
      value_compose_of_mem_function hr hs hi]
  exact substituteMembershipFormula_compose hab ha hb hc (by simpa only [a, stateSource_code] using hφ)

def IsMembershipStateIdentity (s : V) : Prop :=
  stateSource s = stateTarget s ∧ ∀ i ∈ stateSource s, (stateBound s) ‘ i = boundVarCode i

instance membershipStateIdentity_definable : ℒₛₑₜ-predicate[V] IsMembershipStateIdentity := by
  unfold IsMembershipStateIdentity
  definability

theorem IsMembershipStateIdentity.termMap {s : V} (h : IsMembershipStateIdentity s)
    (hs : IsSubstitutionState membershipLanguageCode ∅ ∅ s) :
    membershipStateTermMap s = SetTheory.identity (termSet membershipLanguageCode ∅ (stateSource s)) := by
  have hf := membershipStateTermMap_function hs
  rw [← h.1] at hf
  apply function_eq_of_values hf (identity_mem_function _)
  intro x hx
  rw [identity_value hx]
  obtain ⟨i, hi, rfl⟩ := membershipTerm_cases hs.1 hx
  exact (membershipStateTermMap_boundVar hs hi).trans (h.2 i hi)

theorem IsMembershipStateIdentity.lift {s : V} (h : IsMembershipStateIdentity s)
    (hs : IsSubstitutionState membershipLanguageCode ∅ ∅ s) :
    IsMembershipStateIdentity (liftSubstitutionState membershipLanguageCode ∅ s) := by
  refine ⟨by simpa [liftSubstitutionState] using congrArg succ h.1, ?_⟩
  intro i hi
  have hi' : i ∈ succ (stateSource s) := by simpa only [liftSubstitutionState, stateSource_code] using hi
  have hiω := IsOrdinal.toIsTransitive.mem_trans hi' (ω_succ_closed hs.1)
  simp only [liftSubstitutionState, stateBound_code]
  rcases internalNatural_cases hiω with rfl | ⟨j, hj, rfl⟩
  · exact liftBoundReplacement_zero hs.1 _ _ _ _
  · have hj' : j ∈ stateSource s := by
      have hne : succ j ≠ (0 : V) := by
        intro hz
        have hh : j ∈ succ j := by simp
        rw [hz] at hh
        exact not_mem_empty hh
      have hh := natural_predecessor_mem hs.1 hi' hne
      have : IsOrdinal j := IsOrdinal.of_mem hj
      simpa only [sUnion_succ_of_transitive] using hh
    rw [liftBoundReplacement_succ membershipLanguageCode_valid hs.2.1 hs.1 hs.2.2.1 hj', h.2 j hj',
      termBoundShift_boundVar membershipLanguageCode_valid hs.2.1 ∅ (h.1 ▸ hj')]

theorem IsMembershipStateIdentity.iterated {s k : V} (h : IsMembershipStateIdentity s)
    (hs : IsSubstitutionState membershipLanguageCode ∅ ∅ s) (hk : k ∈ (ω : V)) :
    IsMembershipStateIdentity ((substitutionStates membershipLanguageCode ∅ s) ‘ k) := by
  apply naturalNumber_induction (fun k ↦
    IsMembershipStateIdentity ((substitutionStates membershipLanguageCode ∅ s) ‘ k))
    (by definability) ?_ ?_ k hk
  · simpa only [substitutionStates_zero] using h
  · intro k hk ih
    rw [substitutionStates_succ _ _ _ hk]
    exact ih.lift (substitutionStates_valid membershipLanguageCode_valid hs hk)

theorem substituteMembershipFormula_identity {s φ : V} (h : IsMembershipStateIdentity s)
    (hs : IsSubstitutionState membershipLanguageCode ∅ ∅ s)
    (hφ : φ ∈ formulaSet membershipLanguageCode ∅ (stateSource s)) :
    substituteFormula membershipLanguageCode ∅ ∅ s φ = φ := by
  have hc := formulaSubstitutionGraph_identity (G := substitutionStates membershipLanguageCode ∅ s)
    membershipLanguageCode_valid
    (fun k hk ↦ by simp only [substitutionStates_succ _ _ _ hk, liftSubstitutionState, stateSource_code])
    (fun k hk ↦ (h.iterated hs hk).termMap (substitutionStates_valid membershipLanguageCode_valid hs hk))
    (stateSource s) φ hφ (0 : V) (by simp) (by simp only [substitutionStates_zero])
  exact hc

theorem renameMembershipFormula_identity {n φ : V} (hn : n ∈ (ω : V))
    (hφ : φ ∈ formulaSet membershipLanguageCode ∅ n) :
    renameMembershipFormula n n (SetTheory.identity n) φ = φ := by
  apply substituteMembershipFormula_identity
  · simp only [IsMembershipStateIdentity, stateSource_code, stateTarget_code, stateBound_code, true_and,
      graph_identity_compose (boundVariableAssignment_mem hn)]
    exact fun _ hi ↦ boundVariableAssignment_value hi
  · exact membershipRenaming_state hn hn (identity_mem_function n)
  · simpa only [stateSource_code] using hφ

end ZFVP
