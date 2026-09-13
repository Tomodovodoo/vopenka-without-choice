import ZFVP.ModelTheory.ConstantStructure
import ZFVP.Syntax.FoundationEquality

/-! An internal code for the equality and membership structure on a set. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def membershipTupleRelation (A : V) : V :=
  {s ∈ A ^ (2 : V) ; s ‘ (0 : V) ∈ s ‘ (1 : V)}

theorem mem_membershipTupleRelation_iff (A s : V) :
    s ∈ membershipTupleRelation A ↔ s ∈ A ^ (2 : V) ∧ s ‘ (0 : V) ∈ s ‘ (1 : V) := by
  simp [membershipTupleRelation]

instance membershipTupleRelation_definable : ℒₛₑₜ-function₁[V] membershipTupleRelation := by
  have h : ℒₛₑₜ-relation (fun D A : V ↦ ∀ s,
      s ∈ D ↔ s ∈ A ^ (2 : V) ∧ s ‘ (0 : V) ∈ s ‘ (1 : V)) := by definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = membershipTupleRelation (v 1) ↔ _
  rw [mem_ext_iff]
  simp only [mem_membershipTupleRelation_iff]

theorem membershipTupleRelation_subset (A : V) : membershipTupleRelation A ⊆ A ^ (2 : V) :=
  fun s hs ↦ ((mem_membershipTupleRelation_iff A s).mp hs).1

theorem standardTuple_mem_membershipTupleRelation {A : V} (v : Fin 2 → V) (hv : ∀ i, v i ∈ A) :
    standardTuple v ∈ membershipTupleRelation A ↔ v 0 ∈ v 1 := by
  have hv' : standardTuple v ∈ A ^ (2 : V) := by simpa using standardTuple_mem_function v hv
  rw [mem_membershipTupleRelation_iff, and_iff_right hv']
  simpa using (show (standardTuple v) ‘ (((0 : Fin 2).val : ℕ) : V) ∈
      (standardTuple v) ‘ (((1 : Fin 2).val : ℕ) : V) ↔ v 0 ∈ v 1 by
    rw [value_standardTuple, value_standardTuple])

noncomputable def membershipLanguageCode : V :=
  languageCode ∅ (2 : V) (constantGraph ∅ (2 : V)) (constantGraph (2 : V) (2 : V))

theorem membershipLanguageCode_valid : IsLanguageCode (membershipLanguageCode : V) := by
  apply (isLanguageCode_iff _ _ _ _).mpr
  exact ⟨constantGraph_mem_function _ _ _ (by simp), constantGraph_mem_function _ _ _ (by simp)⟩

noncomputable def membershipInterpretation (A r : V) : V := by
  classical
  exact if r = 0 then equalityRelation A else membershipTupleRelation A

instance membershipInterpretation_definable : ℒₛₑₜ-function₂[V] membershipInterpretation := by
  have h : ℒₛₑₜ-relation₃ (fun D A r : V ↦
      (r = 0 ∧ D = equalityRelation A) ∨ (r ≠ 0 ∧ D = membershipTupleRelation A)) := by definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = membershipInterpretation (v 1) (v 2) ↔ _
  unfold membershipInterpretation
  split <;> simp_all

noncomputable def membershipStructureCode (A : V) : V :=
  structureCode A (constantGraph ∅ ∅)
    (definableGraph (2 : V) (membershipInterpretation A) (by definability))

instance membershipStructureCode_definable : ℒₛₑₜ-function₁[V] membershipStructureCode := by
  have h : ℒₛₑₜ-function₁[V] (fun A ↦
      definableGraph (2 : V) (membershipInterpretation A) (by definability)) := by
    have hrel : ℒₛₑₜ-relation (fun g A : V ↦ ∀ p, p ∈ g ↔
        ∃ r ∈ (2 : V), p = ⟨r, membershipInterpretation A r⟩ₖ) := by definability
    apply Language.Definable.of_iff hrel
    intro v
    change v 0 = definableGraph (2 : V) (membershipInterpretation (v 1)) _ ↔ _
    rw [mem_ext_iff]
    simp only [mem_definableGraph_iff]
  unfold membershipStructureCode
  definability

@[simp] theorem membershipStructureCode_domain (A : V) :
    structureDomain (membershipStructureCode A) = A := by simp [membershipStructureCode]

theorem membershipStructureCode_valid {A : V} (hA : IsNonempty A) :
    IsStructureCode membershipLanguageCode (membershipStructureCode A) := by
  simp only [IsStructureCode, membershipStructureCode, membershipLanguageCode,
    structureDomain_code, structureFunctions_code, structureRelations_code,
    functionSymbols_code, relationSymbols_code, functionArities_code, relationArities_code]
  refine ⟨membershipLanguageCode_valid, True.intro, hA, inferInstance, domain_constantGraph _ _,
    inferInstance, domain_definableGraph _ _ _, ?_, ?_⟩
  · intro f hf
    exact False.elim (not_mem_empty hf)
  · intro r hr
    rw [value_definableGraph _ _ _ hr, value_constantGraph _ _ hr]
    classical
    by_cases hr0 : r = 0
    · simpa [membershipInterpretation, hr0] using equalityRelation_subset A
    · simpa [membershipInterpretation, hr0] using membershipTupleRelation_subset A

noncomputable def membershipSymbol : {k : ℕ} → Language.Set.Rel k → V
  | _, .eq => 0
  | _, .mem => 1

theorem membershipSymbol_valid {k : ℕ} (r : Language.Set.Rel k) :
    membershipSymbol r ∈ relationSymbols (membershipLanguageCode : V) ∧
      (relationArities (membershipLanguageCode : V)) ‘ (membershipSymbol r) = (k : V) := by
  cases r <;> simp only [membershipSymbol, membershipLanguageCode, relationSymbols_code, relationArities_code]
  all_goals constructor
  · exact natCast_mem_of_lt (show 0 < 2 by decide)
  · exact value_constantGraph _ _ (natCast_mem_of_lt (show 0 < 2 by decide))
  · exact natCast_mem_of_lt (show 1 < 2 by decide)
  · exact value_constantGraph _ _ (natCast_mem_of_lt (show 1 < 2 by decide))

theorem membershipStructureCode_equality (A : V) :
    (structureRelations (membershipStructureCode A)) ‘ (0 : V) = equalityRelation A := by
  simp only [membershipStructureCode, structureRelations_code]
  rw [value_definableGraph _ _ _ (show (0 : V) ∈ (2 : V) by simp)]
  simp [membershipInterpretation]

theorem membershipStructureCode_membership (A : V) :
    (structureRelations (membershipStructureCode A)) ‘ (1 : V) = membershipTupleRelation A := by
  simp only [membershipStructureCode, structureRelations_code]
  rw [value_definableGraph _ _ _ (show (1 : V) ∈ (2 : V) by simp)]
  simp [membershipInterpretation]

end ZFVP



