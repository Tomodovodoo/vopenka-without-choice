import ZFVP.Syntax.MembershipRenamingConstructors

/-! Renaming an internal atomic membership formula renames both variable slots. -/

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem membershipPair_atomic {n r i j : V} (hn : n ∈ (ω : V))
    (hr : r = equalityToken ∨ r = relationToken (0 : V) ∨ r = relationToken (1 : V))
    (hi : i ∈ n) (hj : j ∈ n) :
    IsAtomicArguments membershipLanguageCode ∅ n r (boundPairArguments i j) :=
  (membershipAtomicArguments_iff hn).mpr ⟨hr, i, hi, j, hj, rfl⟩

theorem renameMembershipFormula_atom_pair {n m r a i j : V}
    (hn : n ∈ (ω : V)) (hm : m ∈ (ω : V)) (hr : r ∈ m ^ n)
    (ha : a = equalityToken ∨ a = relationToken (0 : V) ∨ a = relationToken (1 : V))
    (hi : i ∈ n) (hj : j ∈ n) :
    renameMembershipFormula n m r (atomCode a (boundPairArguments i j)) =
      atomCode a (boundPairArguments (r ‘ i) (r ‘ j)) := by
  unfold renameMembershipFormula substituteFormula
  simp only [stateSource_code]
  rw [formulaSubstitutionGraph_atom membershipLanguageCode_valid hn (show (0 : V) ∈ (ω : V) by simp)
    (membershipPair_atomic hn ha hi hj), substitutionStates_zero, stateBound_code, stateFree_code,
    substituted_boundPairArguments hn hi hj,
    value_compose_of_mem_function hr (boundVariableAssignment_mem hm) hi,
    value_compose_of_mem_function hr (boundVariableAssignment_mem hm) hj,
    boundVariableAssignment_value (function_value_mem hr hi),
    boundVariableAssignment_value (function_value_mem hr hj)]
  rfl

end ZFVP
