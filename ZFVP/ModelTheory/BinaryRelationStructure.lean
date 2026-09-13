import ZFVP.ModelTheory.MembershipStructure

/-! An internal structure code for an arbitrary binary relation. The relation
need not agree with ambient membership, and need not be well founded. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def binaryTupleRelation (D E : V) : V :=
  {s ∈ D ^ (2 : V) ; ⟨s ‘ (0 : V), s ‘ (1 : V)⟩ₖ ∈ E}

theorem mem_binaryTupleRelation (D E s : V) :
    s ∈ binaryTupleRelation D E ↔ s ∈ D ^ (2 : V) ∧ ⟨s ‘ (0 : V), s ‘ (1 : V)⟩ₖ ∈ E := by
  simp only [binaryTupleRelation, mem_sep_iff]

instance binaryTupleRelation_definable : ℒₛₑₜ-function₂[V] binaryTupleRelation := by
  have h : ℒₛₑₜ-relation₃[V] (fun R D E ↦ ∀ s,
      s ∈ R ↔ s ∈ D ^ (2 : V) ∧ ⟨s ‘ (0 : V), s ‘ (1 : V)⟩ₖ ∈ E) := by definability
  apply Language.Definable.of_iff h
  intro v
  rw [mem_ext_iff]
  simp only [mem_binaryTupleRelation]
  rfl

theorem binaryTupleRelation_subset (D E : V) : binaryTupleRelation D E ⊆ D ^ (2 : V) :=
  fun s hs ↦ ((mem_binaryTupleRelation D E s).mp hs).1

theorem standardTuple_mem_binaryTupleRelation {D E : V} (v : Fin 2 → V) (hv : ∀ i, v i ∈ D) :
    standardTuple v ∈ binaryTupleRelation D E ↔ ⟨v 0, v 1⟩ₖ ∈ E := by
  have hv' : standardTuple v ∈ D ^ (2 : V) := by simpa using standardTuple_mem_function v hv
  rw [mem_binaryTupleRelation, and_iff_right hv']
  simpa using (show ⟨(standardTuple v) ‘ (((0 : Fin 2).val : ℕ) : V),
      (standardTuple v) ‘ (((1 : Fin 2).val : ℕ) : V)⟩ₖ ∈ E ↔ ⟨v 0, v 1⟩ₖ ∈ E by
    rw [value_standardTuple, value_standardTuple])

noncomputable def binaryRelationInterpretation (D E r : V) : V := by
  classical
  exact if r = 0 then equalityRelation D else binaryTupleRelation D E

instance binaryRelationInterpretation_definable : ℒₛₑₜ-function₃[V] binaryRelationInterpretation := by
  have h : ℒₛₑₜ-relation₄[V] (fun R D E r ↦
      (r = 0 ∧ R = equalityRelation D) ∨ (r ≠ 0 ∧ R = binaryTupleRelation D E)) := by definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = binaryRelationInterpretation (v 1) (v 2) (v 3) ↔ _
  unfold binaryRelationInterpretation
  split <;> simp_all

noncomputable def binaryRelationStructureCode (D E : V) : V :=
  structureCode D (constantGraph ∅ ∅)
    (definableGraph (2 : V) (binaryRelationInterpretation D E) (by definability))

instance binaryRelationStructureCode_definable : ℒₛₑₜ-function₂[V] binaryRelationStructureCode := by
  have h : ℒₛₑₜ-function₂[V] (fun D E ↦
      definableGraph (2 : V) (binaryRelationInterpretation D E) (by definability)) := by
    have hrel : ℒₛₑₜ-relation₃[V] (fun g D E ↦ ∀ p, p ∈ g ↔
        ∃ r ∈ (2 : V), p = ⟨r, binaryRelationInterpretation D E r⟩ₖ) := by definability
    apply Language.Definable.of_iff hrel
    intro v
    rw [mem_ext_iff]
    simp only [mem_definableGraph_iff]
    rfl
  unfold binaryRelationStructureCode
  definability

@[simp] theorem binaryRelationStructureCode_domain (D E : V) :
    structureDomain (binaryRelationStructureCode D E) = D := by simp [binaryRelationStructureCode]

/-- Validity needs only a nonempty carrier. Tuples already restrict the relation
to `D × D`, so the result also permits relation codes with irrelevant extra pairs. -/
theorem binaryRelationStructureCode_valid {D : V} (hD : IsNonempty D) (E : V) :
    IsStructureCode membershipLanguageCode (binaryRelationStructureCode D E) := by
  simp only [IsStructureCode, binaryRelationStructureCode, membershipLanguageCode,
    structureDomain_code, structureFunctions_code, structureRelations_code,
    functionSymbols_code, relationSymbols_code, functionArities_code, relationArities_code]
  refine ⟨membershipLanguageCode_valid, True.intro, hD, inferInstance, domain_constantGraph _ _,
    inferInstance, domain_definableGraph _ _ _, ?_, ?_⟩
  · intro f hf
    exact False.elim (not_mem_empty hf)
  · intro r hr
    rw [value_definableGraph _ _ _ hr, value_constantGraph _ _ hr]
    classical
    by_cases hr0 : r = 0
    · simpa [binaryRelationInterpretation, hr0] using equalityRelation_subset D
    · simpa [binaryRelationInterpretation, hr0] using binaryTupleRelation_subset D E

theorem binaryRelationStructureCode_equality (D E : V) :
    (structureRelations (binaryRelationStructureCode D E)) ‘ (0 : V) = equalityRelation D := by
  simp only [binaryRelationStructureCode, structureRelations_code]
  rw [value_definableGraph _ _ _ (show (0 : V) ∈ (2 : V) by simp)]
  simp [binaryRelationInterpretation]

theorem binaryRelationStructureCode_relation (D E : V) :
    (structureRelations (binaryRelationStructureCode D E)) ‘ (1 : V) = binaryTupleRelation D E := by
  simp only [binaryRelationStructureCode, structureRelations_code]
  rw [value_definableGraph _ _ _ (show (1 : V) ∈ (2 : V) by simp)]
  simp [binaryRelationInterpretation]

/-- A separate type prevents the ambient membership instance from being used
for the represented binary relation. -/
def BinaryRelationDomain (D _E : V) := {x : V // x ∈ D}

instance binaryRelationDomain_setStructure (D E : V) : SetStructure (BinaryRelationDomain D E) where
  mem y x := ⟨x.val, y.val⟩ₖ ∈ E

theorem binaryRelationDomain_mem_iff {D E : V} (x y : BinaryRelationDomain D E) :
    x ∈ y ↔ ⟨x.val, y.val⟩ₖ ∈ E := Iff.rfl

omit [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] in
theorem binaryRelationDomain_nonempty {D E : V} (hD : IsNonempty D) :
    Nonempty (BinaryRelationDomain D E) := by
  obtain ⟨x, hx⟩ := hD.nonempty
  exact ⟨⟨x, hx⟩⟩

end ZFVP
