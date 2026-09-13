import ZFVP.Syntax.FormulaSubstitutionSemantics
import ZFVP.SetTheory.LevelOneTruth
import ZFVP.SetTheory.CompositionLaws

/-! Renaming any internal finite tuple of bound membership variables. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def boundVariableAssignment (m : V) : V :=
  definableGraph m boundVarCode (by definability)

theorem boundVariableAssignment_mem {m : V} (hm : m ∈ (ω : V)) :
    boundVariableAssignment m ∈ termSet membershipLanguageCode ∅ m ^ m := by
  apply definableGraph_mem_function_of_mapsTo
  exact fun i hi ↦ (termSet_closed membershipLanguageCode_valid hm ∅).1 i hi

theorem boundVariableAssignment_value {m i : V} (hi : i ∈ m) :
    (boundVariableAssignment m) ‘ i = boundVarCode i := value_definableGraph _ _ _ hi

noncomputable def renameMembershipFormula (n m r φ : V) : V :=
  substituteFormula membershipLanguageCode ∅ ∅
    (substitutionState n m (compose r (boundVariableAssignment m)) ∅) φ

theorem membershipRenaming_state {n m r : V} (hn : n ∈ (ω : V)) (hm : m ∈ (ω : V))
    (hr : r ∈ m ^ n) : IsSubstitutionState membershipLanguageCode ∅ ∅
      (substitutionState n m (compose r (boundVariableAssignment m)) ∅) := by
  simp only [IsSubstitutionState, stateSource_code, stateTarget_code, stateBound_code, stateFree_code]
  exact ⟨hn, hm, compose_function hr (boundVariableAssignment_mem hm), by
    apply mem_function.intro <;> simp⟩

theorem renameMembershipFormula_mem {n m r φ : V} (hn : n ∈ (ω : V)) (hm : m ∈ (ω : V))
    (hr : r ∈ m ^ n) (hφ : φ ∈ formulaSet membershipLanguageCode ∅ n) :
    renameMembershipFormula n m r φ ∈ formulaSet membershipLanguageCode ∅ m := by
  have hs := substituteFormula_mem (φ := φ) membershipLanguageCode_valid
    (membershipRenaming_state hn hm hr) (by simpa only [stateSource_code] using hφ)
  simpa only [stateTarget_code, renameMembershipFormula] using hs

theorem membershipSatisfies_rename {A n m r φ b : V} (hA : IsNonempty A)
    (hn : n ∈ (ω : V)) (hm : m ∈ (ω : V)) (hr : r ∈ m ^ n)
    (hφ : φ ∈ formulaSet membershipLanguageCode ∅ n) (hb : b ∈ A ^ m) :
    MembershipSatisfies A m (renameMembershipFormula n m r φ) b ↔
      MembershipSatisfies A n φ (compose r b) := by
  have hM := membershipStructureCode_valid hA
  have hbM : b ∈ structureDomain (membershipStructureCode A) ^ m := by simpa using hb
  have he : (∅ : V) ∈ structureDomain (membershipStructureCode A) ^ (∅ : V) := by
    apply mem_function.intro <;> simp
  have hT := termEvaluation_mem_function hM hm ∅ hbM he
  have hB := boundVariableAssignment_mem hm
  have hev : compose (boundVariableAssignment m)
      (termEvaluation membershipLanguageCode ∅ m (membershipStructureCode A) b ∅) = b := by
    apply function_eq_of_values (compose_function hB hT) hbM
    intro i hi
    rw [value_compose_of_mem_function hB hT hi, boundVariableAssignment_value hi,
      termEvaluation_boundVar membershipLanguageCode_valid hm ∅ _ _ _ hi]
  have hs := satisfies_substituteFormula (φ := φ) (b := b) hM (membershipRenaming_state hn hm hr) he
    (by simpa only [stateSource_code] using hφ) (by simpa only [stateTarget_code] using hbM)
  simp only [stateTarget_code, stateSource_code, stateFree_code, stateBound_code,
    graph_empty_compose, graph_compose_assoc, hev] at hs
  exact hs

end ZFVP
