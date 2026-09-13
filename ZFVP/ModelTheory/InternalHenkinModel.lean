import ZFVP.ModelTheory.InternalHenkinTruthTable
import ZFVP.ModelTheory.InternalNameTruthEquality

/-! The Henkin construction yields an actual internally countable coded model
of every valid consistent internal open theory, when the ambient ω is standard. -/

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem exists_quotientAssignment_of_standardOmega (hω : Schmerl.HasStandardOmega V)
    {D E n b : V} (hn : n ∈ (ω : V)) (hb : b ∈ internalQuotientCarrier D E ^ n) :
    ∃ a ∈ D ^ n, compose a (internalQuotientProjection D E) = b := by
  obtain ⟨k, rfl⟩ := hω n hn
  have hp : ∀ i : Fin k, ∃ x ∈ D, b ‘ (i.val : V) = internalEquivalenceClass D E x := by
    intro i
    exact (mem_internalQuotientCarrier _ _ _).mp (function_value_mem hb (natCast_mem_of_lt i.isLt))
  choose f hf he using hp
  have ha := standardTuple_mem_function f hf
  refine ⟨standardTuple f, ha, ?_⟩
  apply function_eq_of_values (compose_function ha (internalQuotientProjection_mem D E)) hb
  intro i hi
  obtain ⟨j, rfl⟩ := (mem_natCast_iff i k).mp hi
  rw [quotientAssignment_value ha (natCast_mem_of_lt j.isLt), value_standardTuple]
  exact (he j).symm

noncomputable def internalHenkinModel (T e : V) : V :=
  internalQuotientStructure (ω : V) (henkinNameRelation T (henkinStages T e) (relationToken 0))
    (henkinNameRelation T (henkinStages T e) (relationToken 1))

theorem henkinStages_equality (hω : Schmerl.HasStandardOmega V) {T e : V}
    (hT : EqualityCodedSequentConsistent T)
    (he : e ∈ (formulaFamily (membershipLanguageCode : V) ∅) ^ (ω : V))
    (hrange : range e = formulaFamily (membershipLanguageCode : V) ∅) :
    IsInternalSetoid (ω : V) (henkinNameRelation T (henkinStages T e) (relationToken 0)) ∧
      IsInternalRelationCongruence (ω : V) (henkinNameRelation T (henkinStages T e) (relationToken 0))
        (henkinNameRelation T (henkinStages T e) (relationToken 1)) := by
  apply (henkinStages_isNameTruthTable hω hT he hrange).equality_laws
    (henkinNameRelation_subset _ _ _) (henkinNameRelation_subset _ _ _)
  rw [henkinNameTruthTable_lookup]
  have hs := henkinStages_complete hω hT he hrange
  apply hs.name_axiom hω
  · simpa [zero_def] using encodeMembershipFormula_mem (V := V) equalityBasisSentence
  · exact mem_union_iff.mpr (Or.inr (by simp [canonicalEqualityOpenCodes]))
  · simp [mem_function_iff, zero_def]

theorem internalHenkinModel_valid (T e : V) : IsStructureCode membershipLanguageCode (internalHenkinModel T e) :=
  internalQuotientStructure_valid ⟨0, by simp⟩

theorem internalHenkinModel_countable (T e : V) : IsInternallyCountable (structureDomain (internalHenkinModel T e)) :=
  internalQuotientStructure_countable internallyCountable_omega

theorem internalHenkinModel_models (hω : Schmerl.HasStandardOmega V) {T e : V}
    (hvalid : T ⊆ formulaFamily (membershipLanguageCode : V) ∅)
    (hT : EqualityCodedSequentConsistent T)
    (he : e ∈ (formulaFamily (membershipLanguageCode : V) ∅) ^ (ω : V))
    (hrange : range e = formulaFamily (membershipLanguageCode : V) ∅) :
    SatisfiesCodedOpenTheory membershipLanguageCode (internalHenkinModel T e) T := by
  have hs := henkinStages_complete hω hT he hrange
  have htable := henkinStages_isNameTruthTable hω hT he hrange
  obtain ⟨hE, hR⟩ := henkinStages_equality hω hT he hrange
  refine ⟨internalHenkinModel_valid T e, fun n φ hφT ↦ ?_⟩
  have hφ := (mem_formulaSet_iff _ _ _ _).mpr (hvalid _ hφT)
  have hn := formulaSet_context membershipLanguageCode_valid hφ
  refine ⟨hφ, fun b hb ↦ ?_⟩
  rw [internalHenkinModel, internalQuotientStructure_domain] at hb
  obtain ⟨a, ha, rfl⟩ := exists_quotientAssignment_of_standardOmega hω hn hb
  apply (nameTruthTable_quotient hE hR htable n φ hφ a ha).mp
  rw [henkinNameTruthTable_lookup]
  exact hs.name_axiom hω hφ (mem_union_iff.mpr (Or.inl hφT)) ha

theorem exists_internal_countable_model_of_consistent (hω : Schmerl.HasStandardOmega V) (hAC : InternalChoice V)
    {T : V} (hvalid : T ⊆ formulaFamily (membershipLanguageCode : V) ∅)
    (hT : EqualityCodedSequentConsistent T) :
    ∃ M : V, IsInternallyCountable (structureDomain M) ∧ SatisfiesCodedOpenTheory membershipLanguageCode M T := by
  obtain ⟨e, he, hrange, _⟩ := exists_internal_henkinStages hω hAC hT
  exact ⟨internalHenkinModel T e, internalHenkinModel_countable T e,
    internalHenkinModel_models hω hvalid hT he hrange⟩

end ZFVP
