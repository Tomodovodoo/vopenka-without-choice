import ZFVP.SetTheory.WellOrderedCardinal

/-! Internal cofinality is the least ordinal length of an unbounded map. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

def IsCofinalMap (α β f : V) : Prop :=
  f ∈ α ^ β ∧ ∀ ξ ∈ α, ∃ i ∈ β, ξ ⊆ f ‘ i

instance isCofinalMap_definable : ℒₛₑₜ-relation₃[V] IsCofinalMap := by
  unfold IsCofinalMap
  definability

theorem identity_isCofinalMap (α : V) : IsCofinalMap α α (identity α) := by
  refine ⟨identity_mem_function α, ?_⟩
  intro ξ hξ
  refine ⟨ξ, hξ, ?_⟩
  have hv : (identity α) ‘ ξ = ξ := value_eq_of_kpair_mem (by simp [hξ])
  rw [hv]

def IsCofinality (α κ : V) : Prop := IsOrdinal α ∧ IsLeastOrdinal (fun β ↦ ∃ f, IsCofinalMap α β f) κ

instance isCofinality_definable : ℒₛₑₜ-relation[V] IsCofinality := by
  unfold IsCofinality IsLeastOrdinal
  definability

theorem cofinality_existsUnique (α : V) [IsOrdinal α] : ∃! κ, IsCofinality α κ := by
  obtain ⟨κ, hκ, huniq⟩ := leastOrdinal_existsUnique (fun β ↦ ∃ f, IsCofinalMap α β f) (by definability)
    ⟨α, inferInstance, identity α, identity_isCofinalMap α⟩
  exact ⟨κ, ⟨inferInstance, hκ⟩, fun μ hμ ↦ huniq μ hμ.2⟩

noncomputable def internalCofinality (α : V) : V := by
  classical
  exact if hα : IsOrdinal α then Classical.choose! (@cofinality_existsUnique V _ _ _ α hα) else ∅

theorem internalCofinality_spec (α : V) [IsOrdinal α] : IsCofinality α (internalCofinality α) := by
  simpa [internalCofinality, show IsOrdinal α from inferInstance] using Classical.choose!_spec (cofinality_existsUnique α)

theorem internalCofinality_eq_iff (α κ : V) : internalCofinality α = κ ↔
    IsCofinality α κ ∨ (¬IsOrdinal α ∧ κ = ∅) := by
  by_cases hα : IsOrdinal α
  · have : IsOrdinal α := hα
    simp only [hα, not_true_eq_false, false_and, or_false]
    constructor
    · rintro rfl
      exact internalCofinality_spec α
    · intro hκ
      exact (cofinality_existsUnique α).unique (internalCofinality_spec α) hκ
  · have hn : ¬IsCofinality α κ := fun h ↦ hα h.1
    simp [internalCofinality, hα, hn, eq_comm]

instance internalCofinality_definable : ℒₛₑₜ-function₁[V] internalCofinality := by
  have h : ℒₛₑₜ-relation (fun κ α : V ↦ IsCofinality α κ ∨ (¬IsOrdinal α ∧ κ = ∅)) := by
    definability
  apply Language.Definable.of_iff h
  intro v
  exact eq_comm.trans (internalCofinality_eq_iff (v 1) (v 0))

instance internalCofinality_ordinal (α : V) [IsOrdinal α] : IsOrdinal (internalCofinality α) :=
  (internalCofinality_spec α).2.1

theorem cofinalMap_exists (α : V) [IsOrdinal α] : ∃ f, IsCofinalMap α (internalCofinality α) f :=
  (internalCofinality_spec α).2.2.1

theorem internalCofinality_minimal {α β f : V} [IsOrdinal α] [IsOrdinal β] (hf : IsCofinalMap α β f) :
    internalCofinality α ⊆ β := (internalCofinality_spec α).2.2.2 β inferInstance ⟨f, hf⟩

theorem internalCofinality_subset (α : V) [IsOrdinal α] : internalCofinality α ⊆ α :=
  internalCofinality_minimal (identity_isCofinalMap α)

theorem no_cofinalMap_below_cofinality {α β : V} [IsOrdinal α] (hβ : β ∈ internalCofinality α) :
    ¬∃ f, IsCofinalMap α β f := by
  have : IsOrdinal β := IsOrdinal.of_mem hβ
  rintro ⟨f, hf⟩
  exact mem_irrefl β (internalCofinality_minimal hf β hβ)

end ZFVP
