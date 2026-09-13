import ZFVP.ModelTheory.LanguageCode

/-! Internal structures for arbitrary set-sized first-order languages. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- A universe and the function/relation interpretation graphs, all internal sets. -/
noncomputable def structureCode (A FI RI : V) : V := ⟨A, ⟨FI, RI⟩ₖ⟩ₖ
noncomputable def structureDomain (M : V) : V := kpair.π₁ M
noncomputable def structureFunctions (M : V) : V := kpair.π₁ (kpair.π₂ M)
noncomputable def structureRelations (M : V) : V := kpair.π₂ (kpair.π₂ M)

@[simp] theorem structureDomain_code (A FI RI : V) :
    structureDomain (structureCode A FI RI) = A := by simp [structureDomain, structureCode]
@[simp] theorem structureFunctions_code (A FI RI : V) :
    structureFunctions (structureCode A FI RI) = FI := by simp [structureFunctions, structureCode]
@[simp] theorem structureRelations_code (A FI RI : V) :
    structureRelations (structureCode A FI RI) = RI := by simp [structureRelations, structureCode]

theorem structureCode_injective {A FI RI A' FI' RI' : V} :
    structureCode A FI RI = structureCode A' FI' RI' ↔ A = A' ∧ FI = FI' ∧ RI = RI' := by
  simp [structureCode]

/-- Function symbols are interpreted as total functions on tuples of the specified
arity; relation symbols are interpreted as arbitrary subsets of those tuples. -/
def IsStructureCode (L M : V) : Prop :=
  IsLanguageCode L ∧
  M = structureCode (structureDomain M) (structureFunctions M) (structureRelations M) ∧
  IsNonempty (structureDomain M) ∧
  IsFunction (structureFunctions M) ∧ domain (structureFunctions M) = functionSymbols L ∧
  IsFunction (structureRelations M) ∧ domain (structureRelations M) = relationSymbols L ∧
  (∀ f ∈ functionSymbols L,
    (structureFunctions M) ‘ f ∈ structureDomain M ^ (structureDomain M ^ ((functionArities L) ‘ f))) ∧
  ∀ r ∈ relationSymbols L,
    (structureRelations M) ‘ r ⊆ structureDomain M ^ ((relationArities L) ‘ r)

instance structureCode_definable : ℒₛₑₜ-function₃[V] structureCode := by
  unfold structureCode
  definability
instance structureDomain_definable : ℒₛₑₜ-function₁[V] structureDomain := by
  unfold structureDomain
  definability
instance structureFunctions_definable : ℒₛₑₜ-function₁[V] structureFunctions := by
  unfold structureFunctions
  definability
instance structureRelations_definable : ℒₛₑₜ-function₁[V] structureRelations := by
  unfold structureRelations
  definability
instance isStructureCode_definable : ℒₛₑₜ-relation[V] IsStructureCode := by
  unfold IsStructureCode
  definability

theorem IsStructureCode.language {L M : V} (hM : IsStructureCode L M) : IsLanguageCode L := hM.1

theorem IsStructureCode.domain_nonempty {L M : V} (hM : IsStructureCode L M) :
    IsNonempty (structureDomain M) := hM.2.2.1

theorem IsStructureCode.function_value_mem {L M f s : V} (hM : IsStructureCode L M)
    (hf : f ∈ functionSymbols L)
    (hs : s ∈ structureDomain M ^ ((functionArities L) ‘ f)) :
    ((structureFunctions M) ‘ f) ‘ s ∈ structureDomain M := by
  obtain ⟨_, _, _, _, _, _, _, hfunc, _⟩ := hM
  exact ZFVP.function_value_mem (hfunc f hf) hs

theorem IsStructureCode.relation_tuple_mem {L M r s : V} (hM : IsStructureCode L M)
    (hr : r ∈ relationSymbols L) (hs : s ∈ (structureRelations M) ‘ r) :
    s ∈ structureDomain M ^ ((relationArities L) ‘ r) := by
  obtain ⟨_, _, _, _, _, _, _, _, hrel⟩ := hM
  exact hrel r hr s hs

theorem IsStructureCode.relation_tuple_finite {L M r s : V} (hM : IsStructureCode L M)
    (hr : r ∈ relationSymbols L) (hs : s ∈ (structureRelations M) ‘ r) :
    s ∈ finiteSequences (structureDomain M) :=
  (mem_finiteSequences_iff _ _).mpr ⟨(relationArities L) ‘ r,
    hM.language.relation_arity_natural hr, hM.relation_tuple_mem hr hs⟩

end ZFVP
