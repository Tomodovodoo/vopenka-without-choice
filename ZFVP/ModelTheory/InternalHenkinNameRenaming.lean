import ZFVP.ModelTheory.InternalHenkinNameBooleans

/-! Substitution of finite natural-name assignments, including the binder slot. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem liftMembershipIndices_compose_prepend {n m r U b x : V}
    (hn : n ∈ (ω : V)) (hm : m ∈ (ω : V)) (hr : r ∈ m ^ n) (hb : b ∈ U ^ m) (hx : x ∈ U) :
    compose (liftMembershipIndices n r) (assignmentPrepend m b x) =
      assignmentPrepend n (compose r b) x := by
  have hl := liftMembershipIndices_function hn hm hr
  have hp := assignmentPrepend_mem_function hm hb hx
  apply function_eq_of_values (compose_function hl hp)
    (assignmentPrepend_mem_function hn (compose_function hr hb) hx)
  intro i hi
  rw [value_compose_of_mem_function hl hp hi]
  rcases internalBoundIndex_cases hn hi with rfl | ⟨j, hj, rfl⟩
  · rw [liftMembershipIndices_zero hn, assignmentPrepend_zero hm, assignmentPrepend_zero hn]
  · rw [liftMembershipIndices_succ hn hj, assignmentPrepend_succ hm (function_value_mem hr hj),
      assignmentPrepend_succ hn hj, value_compose_of_mem_function hr hb hj]

theorem reverseIndices_succ_prepend {m : V} (hm : m ∈ (ω : V)) :
    reverseIndices (succ m) = assignmentPrepend m (reverseIndices m) m := by
  apply function_eq_of_values (reverseIndices_omega_function (ω_succ_closed hm))
    (assignmentPrepend_mem_function hm (reverseIndices_omega_function hm) hm)
  intro i hi
  rcases internalBoundIndex_cases hm hi with rfl | ⟨j, hj, rfl⟩
  · rw [reverseIndices_succ_zero hm, assignmentPrepend_zero hm]
  · rw [reverseIndices_succ_succ hm hj, assignmentPrepend_succ hm hj]

theorem liftMembershipIndices_compose_reverse {n m r : V}
    (hn : n ∈ (ω : V)) (hm : m ∈ (ω : V)) (hr : r ∈ m ^ n) :
    compose (liftMembershipIndices n r) (reverseIndices (succ m)) =
      assignmentPrepend n (compose r (reverseIndices m)) m := by
  rw [reverseIndices_succ_prepend hm]
  exact liftMembershipIndices_compose_prepend hn hm hr (reverseIndices_omega_function hm) hm

theorem IsCompleteHenkinSequence.name_rename_iff (hω : Schmerl.HasStandardOmega V)
    {T s n m r φ b : V} (hs : IsCompleteHenkinSequence T s)
    (hn : n ∈ (ω : V)) (hm : m ∈ (ω : V)) (hr : r ∈ m ^ n)
    (hφ : φ ∈ formulaSet membershipLanguageCode ∅ n) (hb : b ∈ (ω : V) ^ m) :
    HenkinNameHolds T s m (renameMembershipFormula n m r φ) b ↔ HenkinNameHolds T s n φ (compose r b) := by
  obtain ⟨l, hl, t, ht, he⟩ := exists_reverseNameAssignment hm hb
  have hnames : compose r b = compose (compose r t) (reverseIndices l) := by
    rw [he, graph_compose_assoc]
  rw [henkinNameHolds_iff_of_rep hω hs (renameMembershipFormula_mem hn hm hr hφ) hl ht he,
    henkinNameHolds_iff_of_rep hω hs hφ hl (compose_function hr ht) hnames,
    renameMembershipFormula_compose hn hm hl hr ht hφ]

theorem IsCompleteHenkinSequence.name_reverse_iff (hω : Schmerl.HasStandardOmega V) {T s n φ : V}
    (hs : IsCompleteHenkinSequence T s) (hφ : φ ∈ formulaSet membershipLanguageCode ∅ n) :
    HenkinNameHolds T s n φ (reverseIndices n) ↔ HenkinAccepted T s ⟨n, φ⟩ₖ := by
  have hn := formulaSet_context membershipLanguageCode_valid hφ
  rw [henkinNameHolds_iff_of_rep hω hs hφ hn (identity_mem_function n)
    (graph_identity_compose (reverseIndices_function hn)).symm, renameMembershipFormula_identity hn hφ]

theorem liftMembershipIndices_compose_instantiate {n m r i : V}
    (hn : n ∈ (ω : V)) (hm : m ∈ (ω : V)) (hr : r ∈ m ^ n) (hi : i ∈ m) :
    compose (liftMembershipIndices n r) (assignmentPrepend m (identity m) i) = assignmentPrepend n r i := by
  rw [liftMembershipIndices_compose_prepend hn hm hr (identity_mem_function m) hi,
    graph_compose_identity hr]

theorem CodedFormulaImplies.instantiate_exists (T : V) {n i φ : V}
    (hn : n ∈ (ω : V)) (hi : i ∈ n) (hφ : φ ∈ formulaSet membershipLanguageCode ∅ (succ n)) :
    CodedFormulaImplies T n (instantiateMembershipFormula n i φ) (existsCode φ) := by
  have ht := renameMembershipFormula_mem (ω_succ_closed hn) hn
    (assignmentPrepend_mem_function hn (identity_mem_function n) hi) hφ
  have he := (formulaSet_quantifiers membershipLanguageCode_valid hn hφ).2
  have hp := StandardCodedProvable.identity (T ∪ canonicalEqualityOpenCodes) hn ht
  have hex := hp.exists ((isCodedSequent_singleton hn
    (negateFormula_mem membershipLanguageCode_valid ht)).insert he) hi hφ
  exact ⟨ht, he, hex.to_internal⟩

end ZFVP
