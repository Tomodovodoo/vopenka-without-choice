import ZFVP.Syntax.MembershipAtomicSemantics

/-! Membership formulas remain valid when additional symbols are added.
The result includes every internally finite formula code. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

def IsMembershipLanguageExtension (L : V) : Prop :=
  IsLanguageCode L ∧ relationSymbols (membershipLanguageCode : V) ⊆ relationSymbols L ∧
    ∀ r : V, r ∈ relationSymbols (membershipLanguageCode : V) →
      (relationArities L) ‘ r = (relationArities (membershipLanguageCode : V)) ‘ r

theorem membershipTermSet_subset {L n : V} (hL : IsLanguageCode L) (hn : n ∈ (ω : V)) :
    termSet membershipLanguageCode ∅ n ⊆ termSet L ∅ n := by
  intro t ht
  obtain ⟨i, hi, rfl⟩ := membershipTerm_cases hn ht
  exact (termSet_closed hL hn ∅).1 i hi

theorem membershipAtomicArguments_extension {L n r args : V}
    (hL : IsMembershipLanguageExtension L) (hn : n ∈ (ω : V))
    (ha : IsAtomicArguments membershipLanguageCode ∅ n r args) :
    IsAtomicArguments L ∅ n r args := by
  rcases ha with ⟨hr, ha⟩ | ⟨s, hs, hr, ha⟩
  · exact Or.inl ⟨hr, mem_function_of_mem_function_of_subset ha (membershipTermSet_subset hL.1 hn)⟩
  · refine Or.inr ⟨s, hL.2.1 s hs, hr, ?_⟩
    rw [hL.2.2 s hs]
    exact mem_function_of_mem_function_of_subset ha (membershipTermSet_subset hL.1 hn)

theorem membershipFormulaSet_subset {L : V} (hL : IsMembershipLanguageExtension L) (n : V) :
    formulaSet membershipLanguageCode ∅ n ⊆ formulaSet L ∅ n := by
  have hi := formulaSet_induction membershipLanguageCode_valid ∅
    (fun n φ ↦ φ ∈ formulaSet L ∅ n) (by definability)
    (fun n hn ↦ formulaSet_constants hL.1 hn ∅)
    (fun n hn _ _ ha ↦ formulaSet_atoms hL.1 hn (membershipAtomicArguments_extension hL hn ha))
    (fun n hn _ _ _ _ hφ hψ ↦ formulaSet_binary hL.1 hn hφ hψ)
    (fun n hn _ _ hφ ↦ formulaSet_quantifiers hL.1 hn hφ)
  exact fun φ hφ ↦ hi n φ hφ

theorem membershipEvaluatedArguments_extension {L n args k : V}
    (hL : IsLanguageCode L) (hn : n ∈ (ω : V)) (M N b : V)
    (ha : args ∈ termSet membershipLanguageCode ∅ n ^ k) :
    evaluatedArguments L ∅ M ∅ n b args =
      evaluatedArguments membershipLanguageCode ∅ N ∅ n b args := by
  unfold evaluatedArguments evaluateWithFreeAssignment
  apply mem_ext
  intro p
  constructor
  · intro hp
    obtain ⟨i, t, x, hit, htx, rfl⟩ := mem_compose_iff.mp hp
    obtain ⟨j, hj, rfl⟩ := membershipTerm_cases hn (mem_of_mem_functions ha hit).2
    have hx : b ‘ j = x := (termEvaluation_boundVar hL hn ∅ M b ∅ hj).symm.trans
      (value_eq_of_kpair_mem htx)
    apply mem_compose_iff.mpr
    refine ⟨i, boundVarCode j, x, hit, kpair_mem_iff_value.mpr ⟨?_, ?_⟩, rfl⟩
    · rw [domain_termEvaluation]
      exact (termSet_closed membershipLanguageCode_valid hn ∅).1 j hj
    · exact (termEvaluation_boundVar membershipLanguageCode_valid hn ∅ N b ∅ hj).trans hx
  · intro hp
    obtain ⟨i, t, x, hit, htx, rfl⟩ := mem_compose_iff.mp hp
    obtain ⟨j, hj, rfl⟩ := membershipTerm_cases hn (mem_of_mem_functions ha hit).2
    have hx : b ‘ j = x := (termEvaluation_boundVar membershipLanguageCode_valid hn ∅ N b ∅ hj).symm.trans
      (value_eq_of_kpair_mem htx)
    apply mem_compose_iff.mpr
    refine ⟨i, boundVarCode j, x, hit, kpair_mem_iff_value.mpr ⟨?_, ?_⟩, rfl⟩
    · rw [domain_termEvaluation]
      exact (termSet_closed hL hn ∅).1 j hj
    · exact (termEvaluation_boundVar hL hn ∅ M b ∅ hj).trans hx

end ZFVP
