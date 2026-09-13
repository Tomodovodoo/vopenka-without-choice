import ZFVP.ModelTheory.InternalNamedTruthTable
import ZFVP.ModelTheory.InternalNameTruthEquality
import ZFVP.ModelTheory.InternalNamedHenkinExistence
import ZFVP.ModelTheory.InternalBinaryQuotientDefinability

/-! The actual internal Henkin quotient of a finitely source-realizable named
background. The source's elementary diagram gives an actual elementary map. -/

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def namedTheoryModel (T : V) : V :=
  internalQuotientStructure (ω : V) (namedTableRelation T (relationToken 0))
    (namedTableRelation T (relationToken 1))

noncomputable def namedTheoryProjection (T : V) : V :=
  internalQuotientProjection (ω : V) (namedTableRelation T (relationToken 0))

instance namedTheoryModel_definable : ℒₛₑₜ-function₁[V] namedTheoryModel := by
  unfold namedTheoryModel
  definability

instance namedTheoryProjection_definable : ℒₛₑₜ-function₁[V] namedTheoryProjection := by
  unfold namedTheoryProjection
  definability

theorem namedTheoryModel_valid (T : V) : IsStructureCode membershipLanguageCode (namedTheoryModel T) :=
  internalQuotientStructure_valid ⟨(0 : V), by simp⟩

theorem namedTheoryModel_countable (T : V) : IsInternallyCountable (structureDomain (namedTheoryModel T)) :=
  internalQuotientStructure_countable internallyCountable_omega

theorem namedTheoryProjection_mem (T : V) : namedTheoryProjection T ∈ structureDomain (namedTheoryModel T) ^ (ω : V) := by
  simpa only [namedTheoryModel, namedTheoryProjection, internalQuotientStructure_domain] using
    internalQuotientProjection_mem (ω : V) (namedTableRelation T (relationToken 0))

namespace IsCompleteNamedTheory

theorem background_subset {L M j B T : V} (h : IsCompleteNamedTheory L M j B T)
    (hL : IsLanguageCode L) : B ⊆ T := by
  intro p hp
  have hv := h.finite.1 p (mem_union_iff.mpr (Or.inl hp))
  rcases h.complete p hv with ht | ht
  · exact ht
  · exfalso
    obtain ⟨f, hf, hh⟩ := h.finite.2 {p, namedNegation L p}
      (by simpa using internallyFinite_insert (internallyFinite_insert internallyFinite_empty (namedNegation L p)) p)
      (by
        intro q hq
        have hq' : q = p ∨ q = namedNegation L p := by simpa using hq
        rcases hq' with rfl | rfl
        · exact mem_union_iff.mpr (Or.inl hp)
        · exact mem_union_iff.mpr (Or.inr ht))
    exact ((namedHolds_negation hL hf.1 hv).mp (hh _ (by simp))) (hh p (by simp))

theorem equality_basis {D R j B T : V}
    (h : IsCompleteNamedTheory membershipLanguageCode (binaryRelationStructureCode D R) j B T)
    (hD : IsNonempty D) : TableHolds T 0 (encodeMembershipFormula equalityBasisSentence) ∅ := by
  apply h.source_universal membershipLanguageCode_valid (encodeMembershipFormula_mem equalityBasisSentence)
    (by simp [mem_function_iff, zero_def])
  intro c hc
  have hc0 : c = (∅ : V) := function_eq_of_values hc
    (by simp [mem_function_iff, zero_def]) (fun i hi ↦ False.elim (not_mem_empty hi))
  subst c
  exact (satisfies_encodeBinaryRelationFormula hD equalityBasisSentence
    (![] : Fin 0 → BinaryRelationDomain D R)).mpr eval_equalityBasisSentence

theorem equality_laws {D R j B T : V}
    (h : IsCompleteNamedTheory membershipLanguageCode (binaryRelationStructureCode D R) j B T)
    (hD : IsNonempty D) :
    IsInternalSetoid (ω : V) (namedTableRelation T (relationToken 0)) ∧
      IsInternalRelationCongruence (ω : V) (namedTableRelation T (relationToken 0))
        (namedTableRelation T (relationToken 1)) :=
  (h.nameTruthTable hD).equality_laws (namedTableRelation_subset _ _) (namedTableRelation_subset _ _)
    (h.equality_basis hD)

theorem model_truth {D R j B T n φ b : V}
    (h : IsCompleteNamedTheory membershipLanguageCode (binaryRelationStructureCode D R) j B T)
    (hD : IsNonempty D) (hφ : φ ∈ formulaSet membershipLanguageCode ∅ n) (hb : b ∈ (ω : V) ^ n) :
    TableHolds T n φ b ↔ Satisfies membershipLanguageCode ∅ (namedTheoryModel T) ∅ n φ
      (compose b (namedTheoryProjection T)) :=
  nameTruthTable_quotient (h.equality_laws hD).1 (h.equality_laws hD).2 (h.nameTruthTable hD) n φ hφ b hb

theorem model_named_truth {D R j B T p : V}
    (h : IsCompleteNamedTheory membershipLanguageCode (binaryRelationStructureCode D R) j B T)
    (hD : IsNonempty D) (hp : p ∈ namedFormulaSet membershipLanguageCode (ω : V)) :
    p ∈ T ↔ NamedHolds membershipLanguageCode (namedTheoryModel T) (namedTheoryProjection T) p := by
  obtain ⟨n, _, φ, hφ, b, hb, rfl⟩ := namedFormulaSet_cases membershipLanguageCode_valid hp
  rw [namedHolds_pair]
  exact h.model_truth hD hφ hb

theorem model_background {D R j B T : V}
    (h : IsCompleteNamedTheory membershipLanguageCode (binaryRelationStructureCode D R) j B T)
    (hD : IsNonempty D) :
    ∀ p ∈ B, NamedHolds membershipLanguageCode (namedTheoryModel T) (namedTheoryProjection T) p := by
  intro p hp
  exact (h.model_named_truth hD (h.finite.1 p (mem_union_iff.mpr (Or.inl hp)))).mp
    (h.background_subset membershipLanguageCode_valid p hp)

theorem model_elementary {D R j B T : V}
    (h : IsCompleteNamedTheory membershipLanguageCode (binaryRelationStructureCode D R) j B T)
    (hD : IsNonempty D) (hj : j ∈ (ω : V) ^ D)
    (hd : namedElementaryDiagram membershipLanguageCode (binaryRelationStructureCode D R) j ⊆ B) :
    IsCodedElementaryEmbedding membershipLanguageCode (binaryRelationStructureCode D R)
      (namedTheoryModel T) (compose j (namedTheoryProjection T)) := by
  apply namedDiagram_quotient_elementary (binaryRelationStructureCode_valid hD R)
    (by simpa only [binaryRelationStructureCode_domain] using hj)
    (h.equality_laws hD).1 (h.equality_laws hD).2 (h.nameTruthTable hD)
  intro p hp
  have hpT := h.background_subset membershipLanguageCode_valid p (hd p hp)
  obtain ⟨n, _, φ, _, b, _, rfl, _⟩ := namedElementaryDiagram_cases membershipLanguageCode_valid hp
  simpa only [TableHolds, kpair.π₁_kpair, kpair.π₂_kpair] using hpT

theorem model_codedZF {D R j B T : V}
    (h : IsCompleteNamedTheory membershipLanguageCode (binaryRelationStructureCode D R) j B T)
    (hM : IsCodedZFModel (binaryRelationStructureCode D R)) (hj : j ∈ (ω : V) ^ D)
    (hd : namedElementaryDiagram membershipLanguageCode (binaryRelationStructureCode D R) j ⊆ B) :
    IsCodedZFModel (namedTheoryModel T) := by
  have hD : IsNonempty D := by simpa only [binaryRelationStructureCode_domain] using hM.valid.domain_nonempty
  exact ((h.model_elementary hD hj hd).isCodedZFModel_iff).mp hM

end IsCompleteNamedTheory

theorem exists_named_countable_model (hAC : InternalChoice V) {D R j B : V}
    (hD : IsNonempty D) (hj : j ∈ (ω : V) ^ D)
    (hB : FinitelySourceRealized membershipLanguageCode (binaryRelationStructureCode D R) j B)
    (hfr : HasFreshBackgroundNames j B) :
    ∃ T : V, IsCompleteNamedTheory membershipLanguageCode (binaryRelationStructureCode D R) j B T ∧
      IsStructureCode membershipLanguageCode (namedTheoryModel T) ∧
      IsInternallyCountable (structureDomain (namedTheoryModel T)) ∧
      ∀ p ∈ B, NamedHolds membershipLanguageCode (namedTheoryModel T) (namedTheoryProjection T) p := by
  have hF : IsInternallyCountable (functionSymbols (membershipLanguageCode : V)) := by
    simpa [membershipLanguageCode] using (internallyCountable_empty (V := V))
  have hR : IsInternallyCountable (relationSymbols (membershipLanguageCode : V)) := by
    have hc : IsInternallyCountable (2 : V) := internallyCountable_subset internallyCountable_omega
      (IsOrdinal.toIsTransitive.transitive (2 : V) (by simp))
    simpa [membershipLanguageCode] using hc
  obtain ⟨T, hT⟩ := exists_completeNamedTheory hAC membershipLanguageCode_valid hF hR
    (by simpa only [binaryRelationStructureCode_domain] using hj) hB hfr
  exact ⟨T, hT, namedTheoryModel_valid T, namedTheoryModel_countable T, hT.model_background hD⟩

theorem exists_named_countable_elementary_extension (hAC : InternalChoice V) {D R j B : V}
    (hM : IsCodedZFModel (binaryRelationStructureCode D R)) (hj : j ∈ (ω : V) ^ D)
    (hB : FinitelySourceRealized membershipLanguageCode (binaryRelationStructureCode D R) j B)
    (hfr : HasFreshBackgroundNames j B)
    (hd : namedElementaryDiagram membershipLanguageCode (binaryRelationStructureCode D R) j ⊆ B) :
    ∃ T : V, IsCompleteNamedTheory membershipLanguageCode (binaryRelationStructureCode D R) j B T ∧
      IsCodedZFModel (namedTheoryModel T) ∧ IsInternallyCountable (structureDomain (namedTheoryModel T)) ∧
      IsCodedElementaryEmbedding membershipLanguageCode (binaryRelationStructureCode D R)
        (namedTheoryModel T) (compose j (namedTheoryProjection T)) ∧
      ∀ p ∈ B, NamedHolds membershipLanguageCode (namedTheoryModel T) (namedTheoryProjection T) p := by
  have hD : IsNonempty D := by simpa only [binaryRelationStructureCode_domain] using hM.valid.domain_nonempty
  obtain ⟨T, hT, _, hc, hb⟩ := exists_named_countable_model hAC hD hj hB hfr
  exact ⟨T, hT, hT.model_codedZF hM hj hd, hc, hT.model_elementary hD hj hd, hb⟩

end ZFVP
