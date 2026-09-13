import ZFVP.ModelTheory.InternalHenkinNameAtoms
import ZFVP.ModelTheory.InternalHenkinNameQuantifiers
import ZFVP.ModelTheory.InternalBinaryQuotientTruth

/-! All eight constructor clauses hold for the actual internal Henkin table. -/

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem IsCompleteHenkinSequence.name_atom_iff (hω : Schmerl.HasStandardOmega V) {T s n b r args : V}
    (hs : IsCompleteHenkinSequence T s) (hn : n ∈ (ω : V)) (hb : b ∈ (ω : V) ^ n)
    (ha : IsMembershipAtomicArguments n r args) :
    HenkinNameHolds T s n (atomCode r args) b ↔
      DirectNameAtomicHolds (henkinNameRelation T s (relationToken 0))
        (henkinNameRelation T s (relationToken 1)) n b r args := by
  constructor
  · intro h
    obtain ⟨hr, i, hi, j, hj, rfl⟩ := ha
    have hh := (hs.name_atom_pair_iff hω hn hb hr hi hj).mp h
    refine ⟨i, hi, j, hj, rfl, ?_⟩
    rcases hr with rfl | rfl | rfl
    · rw [hs.nameRelations_equality hω] at hh
      exact Or.inl ⟨Or.inl rfl, hh⟩
    · exact Or.inl ⟨Or.inr rfl, hh⟩
    · exact Or.inr ⟨rfl, hh⟩
  · rintro ⟨i, hi, j, hj, rfl, h⟩
    rcases h with ⟨hr, hh⟩ | ⟨rfl, hh⟩
    · rcases hr with rfl | rfl
      · rw [← hs.nameRelations_equality hω] at hh
        exact (hs.name_atom_pair_iff hω hn hb (Or.inl rfl) hi hj).mpr hh
      · exact (hs.name_atom_pair_iff hω hn hb (Or.inr (Or.inl rfl)) hi hj).mpr hh
    · exact (hs.name_atom_pair_iff hω hn hb (Or.inr (Or.inr rfl)) hi hj).mpr hh

theorem henkinStages_isNameTruthTable (hω : Schmerl.HasStandardOmega V) {T e : V}
    (hT : EqualityCodedSequentConsistent T)
    (he : e ∈ (formulaFamily (membershipLanguageCode : V) ∅) ^ (ω : V))
    (hrange : range e = formulaFamily (membershipLanguageCode : V) ∅) :
    IsNameTruthTable (ω : V) (henkinNameRelation T (henkinStages T e) (relationToken 0))
      (henkinNameRelation T (henkinStages T e) (relationToken 1)) (henkinNameTruthTable T (henkinStages T e)) := by
  have hs := henkinStages_complete hω hT he hrange
  intro n hn b hb
  unfold NameTruthClauses
  simp only [henkinNameTruthTable_lookup]
  refine ⟨⟨hs.name_truth hω hn hb, hs.name_not_falsity hω hn hb⟩, ?_, ?_, ?_⟩
  · intro r args ha
    have ha' := (membershipAtomicArguments_iff hn).mpr ha
    have hatom := (formulaSet_atoms membershipLanguageCode_valid hn ha').1
    have hneg := hs.name_negate_iff hω hatom hb
    rw [negateFormula_atom membershipLanguageCode_valid hn ha', hs.name_atom_iff hω hn hb ha] at hneg
    exact ⟨hs.name_atom_iff hω hn hb ha, hneg⟩
  · intro φ ψ hφ hψ
    exact ⟨hs.name_and_iff hω hφ.valid hψ.valid hb, hs.name_or_iff hω hφ.valid hψ.valid hb⟩
  · intro φ hφ
    exact ⟨henkinStages_name_all_iff hω hT he hrange hn hφ.valid hb,
      henkinStages_name_exists_iff hω hT he hrange hn hφ.valid hb⟩

end ZFVP
