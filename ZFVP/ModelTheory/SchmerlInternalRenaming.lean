import ZFVP.ModelTheory.SchmerlInternalSubstitution
import ZFVP.Syntax.UniformMembershipRenaming

/-! Renaming arbitrary internal finite variable tuples in a coded
infinitary fragment, for any internal language. This constructs syntax
and proves its semantics; it is not an assumed renaming rule. -/

namespace ZFVP.Infinitary.Internal
open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def renamingState (n m r : V) : V :=
  substitutionState n m (compose r (boundVariableAssignment m)) ∅

instance renamingState_definable : ℒₛₑₜ-function₃[V] renamingState := by
  unfold renamingState substitutionState
  have hB : ℒₛₑₜ-function₁[V] boundVariableAssignment := boundVariableAssignmentFormula_defined.to_definable
  let := hB
  definability

theorem boundVariableAssignment_mem_language {L m : V} (hL : IsLanguageCode L) (hm : m ∈ (ω : V)) :
    boundVariableAssignment m ∈ termSet L ∅ m ^ m := by
  apply definableGraph_mem_function_of_mapsTo
  exact fun i hi ↦ (termSet_closed hL hm ∅).1 i hi

theorem renamingState_valid {L n m r : V} (hL : IsLanguageCode L)
    (hn : n ∈ (ω : V)) (hm : m ∈ (ω : V)) (hr : r ∈ m ^ n) :
    IsSubstitutionState L ∅ ∅ (renamingState n m r) := by
  simp only [renamingState, IsSubstitutionState, stateSource_code, stateTarget_code, stateBound_code, stateFree_code]
  exact ⟨hn, hm, compose_function hr (boundVariableAssignment_mem_language hL hm),
    mem_function.intro (by simp) (by simp)⟩

noncomputable def renameCode (L F n m r φ : V) : V := substituteCode L F (renamingState n m r) φ

noncomputable def renamedFragment (L F n m r : V) : V := substitutionFragment L F (renamingState n m r)

theorem renamedFragment_valid {L F n m r : V} (hF : IsFragment L F)
    (hn : n ∈ (ω : V)) (hm : m ∈ (ω : V)) (hr : r ∈ m ^ n) :
    IsFragment L (renamedFragment L F n m r) :=
  substitutionFragment_valid hF (renamingState_valid hF.1 hn hm hr)

theorem renamedFragment_countable {L F n m r : V} (hF : IsInternallyCountable F) :
    IsInternallyCountable (renamedFragment L F n m r) := substitutionFragment_countable hF

theorem renameCode_mem {L F n m r φ : V} (hφ : ⟨n, φ⟩ₖ ∈ F) :
    ⟨m, renameCode L F n m r φ⟩ₖ ∈ renamedFragment L F n m r := by
  simpa only [renamingState, stateSource_code, stateTarget_code, renameCode, renamedFragment] using
    (substituteCode_mem (L := L) (s := renamingState n m r) (by simpa only [renamingState, stateSource_code] using hφ))

theorem holds_renameCode {L F M n m r φ b : V} (hF : IsFragment L F) (hM : IsStructureCode L M)
    (hn : n ∈ (ω : V)) (hm : m ∈ (ω : V)) (hr : r ∈ m ^ n)
    (hφ : ⟨n, φ⟩ₖ ∈ F) (hb : b ∈ structureDomain M ^ m) :
    Holds L (renamedFragment L F n m r) M m (renameCode L F n m r φ) b ↔
      Holds L F M n φ (compose r b) := by
  have he : (∅ : V) ∈ structureDomain M ^ (∅ : V) := mem_function.intro (by simp) (by simp)
  have hT := termEvaluation_mem_function hM hm ∅ hb he
  have hB := boundVariableAssignment_mem_language hF.1 hm
  have hev : compose (boundVariableAssignment m) (termEvaluation L ∅ m M b ∅) = b := by
    apply function_eq_of_values (compose_function hB hT) hb
    intro i hi
    rw [value_compose_of_mem_function hB hT hi, boundVariableAssignment_value hi,
      termEvaluation_boundVar hF.1 hm ∅ M b ∅ hi]
  have h := holds_substituteCode hF hM (renamingState_valid hF.1 hn hm hr)
    (by simpa only [renamingState, stateSource_code] using hφ)
    (by simpa only [renamingState, stateTarget_code] using hb)
  simpa only [renameCode, renamedFragment, renamingState, stateSource_code, stateTarget_code,
    stateBound_code, graph_compose_assoc, hev] using h

end ZFVP.Infinitary.Internal
