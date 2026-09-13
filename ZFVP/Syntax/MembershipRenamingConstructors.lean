import ZFVP.Syntax.MembershipRenamingComposition
import ZFVP.Syntax.FormulaSubstitutionConstructors

/-! Renaming beneath a binder fixes zero and raises every old index. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def liftMembershipIndices (n r : V) : V :=
  assignmentPrepend n (definableGraph n (fun i ↦ succ (r ‘ i)) (by definability)) 0

instance liftMembershipIndices_definable : ℒₛₑₜ-function₂[V] liftMembershipIndices := by
  have hG : ℒₛₑₜ-function₂[V] (fun n r ↦ definableGraph n (fun i ↦ succ (r ‘ i)) (by definability)) := by
    have he : ℒₛₑₜ-relation₃[V] (fun A n r ↦ ∀ p, p ∈ A ↔ ∃ i ∈ n, p = ⟨i, succ (r ‘ i)⟩ₖ) := by
      definability
    apply Language.Definable.of_iff he
    intro v
    change v 0 = definableGraph (v 1) (fun i ↦ succ ((v 2) ‘ i)) _ ↔ _
    rw [mem_ext_iff]
    simp only [mem_definableGraph_iff]
  unfold liftMembershipIndices
  definability

theorem liftMembershipIndices_zero {n : V} (hn : n ∈ (ω : V)) (r : V) :
    (liftMembershipIndices n r) ‘ (0 : V) = 0 := assignmentPrepend_zero hn _ _

theorem liftMembershipIndices_succ {n i : V} (hn : n ∈ (ω : V)) (hi : i ∈ n) (r : V) :
    (liftMembershipIndices n r) ‘ (succ i) = succ (r ‘ i) := by
  rw [liftMembershipIndices, assignmentPrepend_succ hn hi, value_definableGraph _ _ _ hi]

theorem liftMembershipIndices_function {n m r : V} (hn : n ∈ (ω : V)) (hm : m ∈ (ω : V))
    (hr : r ∈ m ^ n) : liftMembershipIndices n r ∈ (succ m) ^ (succ n) := by
  apply assignmentPrepend_mem_function hn
  · apply definableGraph_mem_function_of_mapsTo
    exact fun i hi ↦ succ_mem_succ_of_natural_mem hm (function_value_mem hr hi)
  · exact zero_mem_succ_natural hm

theorem internalBoundIndex_cases {n i : V} (hn : n ∈ (ω : V)) (hi : i ∈ succ n) :
    i = 0 ∨ ∃ j ∈ n, i = succ j := by
  have hiω := IsOrdinal.toIsTransitive.mem_trans hi (ω_succ_closed hn)
  rcases internalNatural_cases hiω with h | ⟨j, hj, rfl⟩
  · exact Or.inl h
  · right
    refine ⟨j, ?_, rfl⟩
    have hne : succ j ≠ (0 : V) := by
      intro hz
      have hh : j ∈ succ j := by simp
      rw [hz] at hh
      exact not_mem_empty hh
    have hp := natural_predecessor_mem hn hi hne
    have : IsOrdinal j := IsOrdinal.of_mem hj
    simpa only [sUnion_succ_of_transitive] using hp

theorem membershipRenaming_state_lift {n m r : V} (hn : n ∈ (ω : V)) (hm : m ∈ (ω : V))
    (hr : r ∈ m ^ n) :
    liftSubstitutionState membershipLanguageCode ∅
      (substitutionState n m (compose r (boundVariableAssignment m)) ∅) =
    substitutionState (succ n) (succ m)
      (compose (liftMembershipIndices n r) (boundVariableAssignment (succ m))) ∅ := by
  have hB := compose_function hr (boundVariableAssignment_mem hm)
  have hl := liftMembershipIndices_function hn hm hr
  have hb : liftBoundReplacement membershipLanguageCode ∅ m n (compose r (boundVariableAssignment m)) =
      compose (liftMembershipIndices n r) (boundVariableAssignment (succ m)) := by
    apply function_eq_of_values (liftBoundReplacement_mem membershipLanguageCode_valid hm hn hB)
      (compose_function hl (boundVariableAssignment_mem (ω_succ_closed hm)))
    intro i hi
    rw [value_compose_of_mem_function hl (boundVariableAssignment_mem (ω_succ_closed hm)) hi,
      boundVariableAssignment_value (function_value_mem hl hi)]
    rcases internalBoundIndex_cases hn hi with rfl | ⟨j, hj, rfl⟩
    · rw [liftBoundReplacement_zero hn, liftMembershipIndices_zero hn]
    · rw [liftBoundReplacement_succ membershipLanguageCode_valid hm hn hB hj,
        value_compose_of_mem_function hr (boundVariableAssignment_mem hm) hj,
        boundVariableAssignment_value (function_value_mem hr hj),
        termBoundShift_boundVar membershipLanguageCode_valid hm ∅ (function_value_mem hr hj),
        liftMembershipIndices_succ hn hj]
  simp only [liftSubstitutionState, stateSource_code, stateTarget_code, stateBound_code, stateFree_code,
    hb, liftFreeReplacement, graph_empty_compose]

theorem renameMembershipFormula_and {n m r φ ψ : V}
    (hφ : φ ∈ formulaSet membershipLanguageCode ∅ n) (hψ : ψ ∈ formulaSet membershipLanguageCode ∅ n) :
    renameMembershipFormula n m r (andCode φ ψ) =
      andCode (renameMembershipFormula n m r φ) (renameMembershipFormula n m r ψ) :=
  substituteFormula_and membershipLanguageCode_valid (by simpa only [stateSource_code] using hφ)
    (by simpa only [stateSource_code] using hψ)

theorem renameMembershipFormula_or {n m r φ ψ : V}
    (hφ : φ ∈ formulaSet membershipLanguageCode ∅ n) (hψ : ψ ∈ formulaSet membershipLanguageCode ∅ n) :
    renameMembershipFormula n m r (orCode φ ψ) =
      orCode (renameMembershipFormula n m r φ) (renameMembershipFormula n m r ψ) :=
  substituteFormula_or membershipLanguageCode_valid (by simpa only [stateSource_code] using hφ)
    (by simpa only [stateSource_code] using hψ)

theorem renameMembershipFormula_all {n m r φ : V} (hn : n ∈ (ω : V)) (hm : m ∈ (ω : V))
    (hr : r ∈ m ^ n) (hφ : φ ∈ formulaSet membershipLanguageCode ∅ (succ n)) :
    renameMembershipFormula n m r (allCode φ) =
      allCode (renameMembershipFormula (succ n) (succ m) (liftMembershipIndices n r) φ) := by
  unfold renameMembershipFormula
  rw [substituteFormula_all membershipLanguageCode_valid (by simpa only [stateSource_code] using hn)
    (by simpa only [stateSource_code] using hφ), membershipRenaming_state_lift hn hm hr]

theorem renameMembershipFormula_exists {n m r φ : V} (hn : n ∈ (ω : V)) (hm : m ∈ (ω : V))
    (hr : r ∈ m ^ n) (hφ : φ ∈ formulaSet membershipLanguageCode ∅ (succ n)) :
    renameMembershipFormula n m r (existsCode φ) =
      existsCode (renameMembershipFormula (succ n) (succ m) (liftMembershipIndices n r) φ) := by
  unfold renameMembershipFormula
  rw [substituteFormula_exists membershipLanguageCode_valid (by simpa only [stateSource_code] using hn)
    (by simpa only [stateSource_code] using hφ), membershipRenaming_state_lift hn hm hr]

theorem liftMembershipIndices_identity {n : V} (hn : n ∈ (ω : V)) :
    liftMembershipIndices n (SetTheory.identity n) = SetTheory.identity (succ n) := by
  apply function_eq_of_values (liftMembershipIndices_function hn hn (identity_mem_function n)) (identity_mem_function _)
  intro i hi
  rw [identity_value hi]
  rcases internalBoundIndex_cases hn hi with rfl | ⟨j, hj, rfl⟩
  · exact liftMembershipIndices_zero hn _
  · rw [liftMembershipIndices_succ hn hj, identity_value hj]

theorem liftMembershipIndices_compose {n m l r s : V}
    (hn : n ∈ (ω : V)) (hm : m ∈ (ω : V)) (hl : l ∈ (ω : V))
    (hr : r ∈ m ^ n) (hs : s ∈ l ^ m) :
    compose (liftMembershipIndices n r) (liftMembershipIndices m s) =
      liftMembershipIndices n (compose r s) := by
  have hR := liftMembershipIndices_function hn hm hr
  have hS := liftMembershipIndices_function hm hl hs
  apply function_eq_of_values (compose_function hR hS) (liftMembershipIndices_function hn hl (compose_function hr hs))
  intro i hi
  rw [value_compose_of_mem_function hR hS hi]
  rcases internalBoundIndex_cases hn hi with rfl | ⟨j, hj, rfl⟩
  · rw [liftMembershipIndices_zero hn, liftMembershipIndices_zero hm, liftMembershipIndices_zero hn]
  · rw [liftMembershipIndices_succ hn hj,
      liftMembershipIndices_succ hm (function_value_mem hr hj), liftMembershipIndices_succ hn hj,
      value_compose_of_mem_function hr hs hj]

end ZFVP
