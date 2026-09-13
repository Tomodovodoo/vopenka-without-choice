import ZFVP.Syntax.MembershipAtomicSyntax

/-! Atomic membership truth expressed directly using assignment values. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem boundPair_evaluatedArguments {n i j : V} (hn : n ∈ (ω : V)) (hi : i ∈ n) (hj : j ∈ n)
    (M b : V) : evaluatedArguments membershipLanguageCode ∅ M ∅ n b (boundPairArguments i j) =
      standardTuple ![b ‘ i, b ‘ j] := by
  unfold evaluatedArguments evaluateWithFreeAssignment boundPairArguments
  rw [compose_standardTuple]
  · congr 1
    funext k
    refine Fin.cases ?_ (fun k ↦ Fin.cases ?_ (fun l ↦ Fin.elim0 l) k) k
    · exact termEvaluation_boundVar membershipLanguageCode_valid hn ∅ M b ∅ hi
    · exact termEvaluation_boundVar membershipLanguageCode_valid hn ∅ M b ∅ hj
  · intro k
    simp only [domain_termEvaluation]
    have hc := (termSet_closed (membershipLanguageCode_valid (V := V)) hn ∅).1
    exact Fin.cases (hc i hi) (fun k ↦ Fin.cases (hc j hj) (fun l ↦ Fin.elim0 l) k) k

theorem membershipAtomic_logicalEquality {n i j : V} (hn : n ∈ (ω : V)) (hi : i ∈ n) (hj : j ∈ n)
    (A b : V) : AtomicHolds membershipLanguageCode ∅ (membershipStructureCode A) ∅ n b
      equalityToken (boundPairArguments i j) ↔ b ‘ i = b ‘ j := by
  rw [atomicHolds_equality, boundPair_evaluatedArguments hn hi hj]
  change (standardTuple ![b ‘ i, b ‘ j]) ‘ (((0 : Fin 2).val : ℕ) : V) =
    (standardTuple ![b ‘ i, b ‘ j]) ‘ (((1 : Fin 2).val : ℕ) : V) ↔ _
  simp only [value_standardTuple]
  rfl

theorem membershipAtomic_relationEquality {A n b i j : V} (hn : n ∈ (ω : V)) (hi : i ∈ n) (hj : j ∈ n)
    (hb : b ∈ A ^ n) : AtomicHolds membershipLanguageCode ∅ (membershipStructureCode A) ∅ n b
      (relationToken (0 : V)) (boundPairArguments i j) ↔ b ‘ i = b ‘ j := by
  have hr : (0 : V) ∈ relationSymbols membershipLanguageCode :=
    (membershipSymbol_valid (V := V) Language.Set.Rel.eq).1
  rw [atomicHolds_relation, and_iff_right hr, membershipStructureCode_equality,
    boundPair_evaluatedArguments hn hi hj]
  apply standardTuple_mem_equalityRelation
  simpa using And.intro (function_value_mem hb hi) (function_value_mem hb hj)

theorem membershipAtomic_membership {A n b i j : V} (hn : n ∈ (ω : V)) (hi : i ∈ n) (hj : j ∈ n)
    (hb : b ∈ A ^ n) : AtomicHolds membershipLanguageCode ∅ (membershipStructureCode A) ∅ n b
      (relationToken (1 : V)) (boundPairArguments i j) ↔ b ‘ i ∈ b ‘ j := by
  have hr : (1 : V) ∈ relationSymbols membershipLanguageCode :=
    (membershipSymbol_valid (V := V) Language.Set.Rel.mem).1
  rw [atomicHolds_relation, and_iff_right hr, membershipStructureCode_membership,
    boundPair_evaluatedArguments hn hi hj]
  apply standardTuple_mem_membershipTupleRelation
  simpa using And.intro (function_value_mem hb hi) (function_value_mem hb hj)

def DirectMembershipAtomicHolds (n b r args : V) : Prop := ∃ i ∈ n, ∃ j ∈ n,
  args = boundPairArguments i j ∧
    (((r = equalityToken ∨ r = relationToken (0 : V)) ∧ b ‘ i = b ‘ j) ∨
      (r = relationToken (1 : V) ∧ b ‘ i ∈ b ‘ j))

instance directMembershipAtomicHolds_definable : ℒₛₑₜ-relation₄[V] DirectMembershipAtomicHolds := by
  unfold DirectMembershipAtomicHolds equalityToken
  definability

theorem directMembershipAtomicHolds_iff {A n b r args : V} (hn : n ∈ (ω : V)) (hb : b ∈ A ^ n)
    (ha : IsMembershipAtomicArguments n r args) :
    DirectMembershipAtomicHolds n b r args ↔
      AtomicHolds membershipLanguageCode ∅ (membershipStructureCode A) ∅ n b r args := by
  constructor
  · rintro ⟨i, hi, j, hj, rfl, h⟩
    rcases h with ⟨hr, he⟩ | ⟨rfl, hm⟩
    · rcases hr with rfl | rfl
      · exact (membershipAtomic_logicalEquality hn hi hj A b).mpr he
      · exact (membershipAtomic_relationEquality hn hi hj hb).mpr he
    · exact (membershipAtomic_membership hn hi hj hb).mpr hm
  · intro h
    obtain ⟨hr, i, hi, j, hj, rfl⟩ := ha
    refine ⟨i, hi, j, hj, rfl, ?_⟩
    rcases hr with rfl | rfl | rfl
    · exact Or.inl ⟨Or.inl rfl, (membershipAtomic_logicalEquality hn hi hj A b).mp h⟩
    · exact Or.inl ⟨Or.inr rfl, (membershipAtomic_relationEquality hn hi hj hb).mp h⟩
    · exact Or.inr ⟨rfl, (membershipAtomic_membership hn hi hj hb).mp h⟩

end ZFVP
