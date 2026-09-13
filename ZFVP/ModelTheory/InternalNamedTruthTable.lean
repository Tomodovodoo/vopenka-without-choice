import ZFVP.ModelTheory.InternalNamedTableRenaming
import ZFVP.ModelTheory.InternalBinaryQuotientTruth

/-! A completed theory finitely realized in a binary source supplies all raw
truth-table clauses. No standardness assumption on the natural numbers is used. -/

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace IsCompleteNamedTheory

theorem name_logicalEquality_iff {D R j B T b : V}
    (h : IsCompleteNamedTheory membershipLanguageCode (binaryRelationStructureCode D R) j B T)
    (hb : b ∈ (ω : V) ^ (2 : V)) :
    TableHolds T 2 (atomCode equalityToken (boundPairArguments 0 1)) b ↔
      TableHolds T 2 (atomCode (relationToken 0) (boundPairArguments 0 1)) b := by
  have haL : IsAtomicArguments membershipLanguageCode ∅ (2 : V) equalityToken (boundPairArguments 0 1) :=
    membershipPair_atomic (by simp) (Or.inl rfl) (by simp) (by simp)
  have haR : IsAtomicArguments membershipLanguageCode ∅ (2 : V) (relationToken 0) (boundPairArguments 0 1) :=
    membershipPair_atomic (by simp) (Or.inr (Or.inl rfl)) (by simp) (by simp)
  apply h.mem_iff_of_source_equiv membershipLanguageCode_valid
    ((pair_mem_namedFormulaSet_iff membershipLanguageCode_valid).mpr
      ⟨(formulaSet_atoms membershipLanguageCode_valid (by simp) haL).1, hb⟩)
    ((pair_mem_namedFormulaSet_iff membershipLanguageCode_valid).mpr
      ⟨(formulaSet_atoms membershipLanguageCode_valid (by simp) haR).1, hb⟩)
  intro f hf
  have hc := compose_function hb hf.1
  have hc' : compose b f ∈ D ^ (2 : V) := by
    simpa only [binaryRelationStructureCode_domain] using hc
  rw [namedHolds_pair, namedHolds_pair,
    satisfies_atom membershipLanguageCode_valid (by simp) haL hc,
    satisfies_atom membershipLanguageCode_valid (by simp) haR hc,
    binaryAtomic_logicalEquality (by simp) (by simp) (by simp),
    binaryAtomic_relationEquality (by simp) (by simp) (by simp) hc']

theorem nameRelations_equality {D R j B T : V}
    (h : IsCompleteNamedTheory membershipLanguageCode (binaryRelationStructureCode D R) j B T) :
    namedTableRelation T equalityToken = namedTableRelation T (relationToken 0) := by
  apply mem_ext
  intro p
  constructor <;> intro hp
  · obtain ⟨x, hx, y, hy, rfl⟩ := mem_prod_iff.mp (namedTableRelation_subset _ _ _ hp)
    rw [pair_mem_namedTableRelation hx hy] at hp ⊢
    exact (h.name_logicalEquality_iff (standardTuple_mem_function _ (by
      intro k; exact Fin.cases hx (fun k ↦ Fin.cases hy (fun l ↦ Fin.elim0 l) k) k))).mp hp
  · obtain ⟨x, hx, y, hy, rfl⟩ := mem_prod_iff.mp (namedTableRelation_subset _ _ _ hp)
    rw [pair_mem_namedTableRelation hx hy] at hp ⊢
    exact (h.name_logicalEquality_iff (standardTuple_mem_function _ (by
      intro k; exact Fin.cases hx (fun k ↦ Fin.cases hy (fun l ↦ Fin.elim0 l) k) k))).mpr hp

theorem name_atom_iff {D R j B T n b a args : V}
    (h : IsCompleteNamedTheory membershipLanguageCode (binaryRelationStructureCode D R) j B T)
    (hD : IsNonempty D) (hn : n ∈ (ω : V)) (hb : b ∈ (ω : V) ^ n)
    (ha : IsMembershipAtomicArguments n a args) :
    TableHolds T n (atomCode a args) b ↔
      DirectNameAtomicHolds (namedTableRelation T (relationToken 0))
        (namedTableRelation T (relationToken 1)) n b a args := by
  have hM := binaryRelationStructureCode_valid hD R
  constructor
  · intro ht
    obtain ⟨ha, i, hi, k, hk, rfl⟩ := ha
    have he := (h.name_atom_pair_iff hM hn hb ha hi hk).mp ht
    refine ⟨i, hi, k, hk, rfl, ?_⟩
    rcases ha with rfl | rfl | rfl
    · exact Or.inl ⟨Or.inl rfl, h.nameRelations_equality ▸ he⟩
    · exact Or.inl ⟨Or.inr rfl, he⟩
    · exact Or.inr ⟨rfl, he⟩
  · rintro ⟨i, hi, k, hk, rfl, hh⟩
    rcases hh with ⟨ha, he⟩ | ⟨rfl, he⟩
    · rcases ha with rfl | rfl
      · apply (h.name_atom_pair_iff hM hn hb (Or.inl rfl) hi hk).mpr
        exact h.nameRelations_equality.symm ▸ he
      · exact (h.name_atom_pair_iff hM hn hb (Or.inr (Or.inl rfl)) hi hk).mpr he
    · exact (h.name_atom_pair_iff hM hn hb (Or.inr (Or.inr rfl)) hi hk).mpr he

theorem nameTruthTable {D R j B T : V}
    (h : IsCompleteNamedTheory membershipLanguageCode (binaryRelationStructureCode D R) j B T)
    (hD : IsNonempty D) :
    IsNameTruthTable (ω : V) (namedTableRelation T (relationToken 0))
      (namedTableRelation T (relationToken 1)) T := by
  intro n hn b hb
  refine ⟨⟨h.truth_mem membershipLanguageCode_valid hn hb,
    h.falsity_not_mem membershipLanguageCode_valid hn hb⟩, ?_, ?_, ?_⟩
  · intro a args ha
    have ha' := (membershipAtomicArguments_iff hn).mpr ha
    have hφ := (formulaSet_atoms membershipLanguageCode_valid hn ha').1
    refine ⟨h.name_atom_iff hD hn hb ha, ?_⟩
    have hnφ := h.negation_mem_iff membershipLanguageCode_valid
      ((pair_mem_namedFormulaSet_iff membershipLanguageCode_valid).mpr ⟨hφ, hb⟩)
    rw [namedNegation_pair, negateFormula_atom membershipLanguageCode_valid hn ha'] at hnφ
    exact hnφ.trans (not_congr (h.name_atom_iff hD hn hb ha))
  · intro φ ψ hφ hψ
    have hφ' := (mem_formulaSet_iff _ _ _ _).mpr hφ
    have hψ' := (mem_formulaSet_iff _ _ _ _).mpr hψ
    exact ⟨h.and_mem_iff membershipLanguageCode_valid hn hφ' hψ' hb,
      h.or_mem_iff membershipLanguageCode_valid hn hφ' hψ' hb⟩
  · intro φ hφ
    have hφ' := (mem_formulaSet_iff _ _ _ _).mpr hφ
    exact ⟨h.all_mem_iff membershipLanguageCode_valid hn hφ' hb,
      h.exists_mem_iff membershipLanguageCode_valid hn hφ' hb⟩

end IsCompleteNamedTheory
end ZFVP
