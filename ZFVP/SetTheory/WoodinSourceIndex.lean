import ZFVP.SetTheory.OrdinalLeftOne
import ZFVP.SetTheory.FunctionValue

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def woodinSourceIndex (α : V) : V := ordinalAdd (1 : V) α

noncomputable def woodinRecursiveIndex (β : V) : V := by
  classical
  exact if β ∈ (ω : V) then ⋃ˢ β else β

instance woodinSourceIndex_definable : ℒₛₑₜ-function₁[V] woodinSourceIndex := by
  unfold woodinSourceIndex
  definability

instance woodinRecursiveIndex_definable : ℒₛₑₜ-function₁[V] woodinRecursiveIndex := by
  have hd : ℒₛₑₜ-relation (fun g β : V ↦
      (β ∈ (ω : V) ∧ g = ⋃ˢ β) ∨ (β ∉ (ω : V) ∧ g = β)) := by definability
  apply Language.Definable.of_iff hd
  intro v
  change v 0 = woodinRecursiveIndex (v 1) ↔ _
  classical
  by_cases h : v 1 ∈ (ω : V) <;> simp [woodinRecursiveIndex, h]

theorem woodinSourceIndex_zero : woodinSourceIndex (∅ : V) = 1 := ordinalAdd_zero 1

theorem woodinSourceIndex_natural {α : V} (hα : α ∈ (ω : V)) :
    woodinSourceIndex α = succ α := ordinalAdd_one_left_natural hα

theorem woodinSourceIndex_infinite {α : V} [IsOrdinal α] (hα : α ∉ (ω : V)) :
    woodinSourceIndex α = α := ordinalAdd_one_left_infinite hα

instance woodinSourceIndex_ordinal (α : V) [IsOrdinal α] : IsOrdinal (woodinSourceIndex α) := by
  let : IsOrdinal (1 : V) := IsOrdinal.of_mem (show (1 : V) ∈ (ω : V) by simp)
  unfold woodinSourceIndex
  infer_instance

theorem woodinSourceIndex_successor (α : V) [IsOrdinal α] :
    woodinSourceIndex (succ α) = succ (woodinSourceIndex α) := by
  let : IsOrdinal (1 : V) := IsOrdinal.of_mem (show (1 : V) ∈ (ω : V) by simp)
  exact ordinalAdd_succ 1 α

theorem woodinSourceIndex_nonzero (α : V) [IsOrdinal α] : woodinSourceIndex α ≠ ∅ := by
  have h : (∅ : V) ∈ woodinSourceIndex α := subset_ordinalAdd 1 α ∅ (by change (0 : V) ∈ succ 0; simp)
  intro he
  rw [he] at h
  exact not_mem_empty h

theorem woodinRecursiveIndex_sourceIndex (α : V) [IsOrdinal α] :
    woodinRecursiveIndex (woodinSourceIndex α) = α := by
  classical
  by_cases hα : α ∈ (ω : V)
  · rw [woodinSourceIndex_natural hα]
    simp only [woodinRecursiveIndex, ω_succ_closed hα, ↓reduceIte, sUnion_succ_of_transitive]
  · rw [woodinSourceIndex_infinite hα]
    simp only [woodinRecursiveIndex, hα, ↓reduceIte]

theorem woodinSourceIndex_recursiveIndex (β : V) [IsOrdinal β] (hβ : β ≠ ∅) :
    woodinSourceIndex (woodinRecursiveIndex β) = β := by
  classical
  by_cases hn : β ∈ (ω : V)
  · rcases internalNatural_cases hn with hz | ⟨α, hα, rfl⟩
    · exact False.elim (hβ hz)
    · let := IsOrdinal.of_mem hα
      simp only [woodinRecursiveIndex, ω_succ_closed hα, ↓reduceIte, sUnion_succ_of_transitive]
      exact woodinSourceIndex_natural hα
  · simp only [woodinRecursiveIndex, hn, ↓reduceIte]
    exact woodinSourceIndex_infinite hn

instance woodinRecursiveIndex_ordinal (β : V) [IsOrdinal β] : IsOrdinal (woodinRecursiveIndex β) := by
  classical
  by_cases hn : β ∈ (ω : V)
  · rcases internalNatural_cases hn with hz | ⟨α, hα, rfl⟩
    · subst β
      simp [woodinRecursiveIndex, zero_def]
    · let := IsOrdinal.of_mem hα
      simpa only [woodinRecursiveIndex, ω_succ_closed hα, ↓reduceIte, sUnion_succ_of_transitive] using
        (show IsOrdinal α from inferInstance)
  · simpa only [woodinRecursiveIndex, hn, ↓reduceIte] using (show IsOrdinal β from inferInstance)

theorem woodinSourceIndex_mem_iff {α β : V} [IsOrdinal α] [IsOrdinal β] :
    woodinSourceIndex α ∈ woodinSourceIndex β ↔ α ∈ β := by
  constructor
  · intro h
    rcases IsOrdinal.mem_trichotomy α β with hab | he | hba
    · exact hab
    · subst β
      exact False.elim (mem_irrefl _ h)
    · have hh : woodinSourceIndex β ∈ woodinSourceIndex α := ordinalAdd_mem hba
      exact False.elim (mem_asymm h hh)
  · exact ordinalAdd_mem

theorem woodinSourceIndex_injective {α β : V} [IsOrdinal α] [IsOrdinal β]
    (h : woodinSourceIndex α = woodinSourceIndex β) : α = β := by
  have he := congrArg woodinRecursiveIndex h
  simpa only [woodinRecursiveIndex_sourceIndex] using he

theorem woodinRecursiveIndex_mem_iff {β θ : V} [IsOrdinal β] [IsOrdinal θ] (hβ : β ≠ ∅) :
    woodinRecursiveIndex β ∈ θ ↔ β ∈ woodinSourceIndex θ := by
  have he := woodinSourceIndex_mem_iff (α := woodinRecursiveIndex β) (β := θ)
  rw [woodinSourceIndex_recursiveIndex β hβ] at he
  exact he.symm

theorem woodinSourceIndex_limit (θ : V) [IsOrdinal θ] (h0 : ∅ ∈ θ)
    (hlim : ∀ α ∈ θ, succ α ∈ θ) : woodinSourceIndex θ = θ := by
  apply woodinSourceIndex_infinite
  intro hn
  rcases internalNatural_cases hn with hz | ⟨α, _, he⟩
  · rw [hz] at h0
    exact not_mem_empty h0
  · rw [he] at hlim
    exact mem_irrefl (succ α) (hlim α (mem_succ_self α))

noncomputable def woodinSourceIndices (θ : V) : V := {β ∈ woodinSourceIndex θ ; β ≠ ∅}

theorem mem_woodinSourceIndices {β θ : V} :
    β ∈ woodinSourceIndices θ ↔ β ∈ woodinSourceIndex θ ∧ β ≠ ∅ := mem_sep_iff

theorem woodinSourceIndex_mem_indices {α θ : V} [IsOrdinal θ] (hα : α ∈ θ) :
    woodinSourceIndex α ∈ woodinSourceIndices θ := by
  let := IsOrdinal.of_mem hα
  exact mem_woodinSourceIndices.mpr ⟨woodinSourceIndex_mem_iff.mpr hα, woodinSourceIndex_nonzero α⟩

theorem woodinRecursiveIndex_mem_of_indices {β θ : V} [IsOrdinal θ]
    (hβ : β ∈ woodinSourceIndices θ) : woodinRecursiveIndex β ∈ θ := by
  have hh := mem_woodinSourceIndices.mp hβ
  let := IsOrdinal.of_mem hh.1
  exact (woodinRecursiveIndex_mem_iff hh.2).mpr hh.1

noncomputable def woodinSourceIndexMap (θ : V) : V :=
  definableGraph θ woodinSourceIndex woodinSourceIndex_definable

noncomputable def woodinRecursiveIndexMap (θ : V) : V :=
  definableGraph (woodinSourceIndices θ) woodinRecursiveIndex woodinRecursiveIndex_definable

theorem woodinSourceIndexMap_function (θ : V) [IsOrdinal θ] :
    woodinSourceIndexMap θ ∈ woodinSourceIndices θ ^ θ :=
  definableGraph_mem_function_of_mapsTo _ _ _ _ (fun _ h ↦ woodinSourceIndex_mem_indices h)

theorem woodinRecursiveIndexMap_function (θ : V) [IsOrdinal θ] :
    woodinRecursiveIndexMap θ ∈ θ ^ woodinSourceIndices θ :=
  definableGraph_mem_function_of_mapsTo _ _ _ _ (fun _ h ↦ woodinRecursiveIndex_mem_of_indices h)

theorem woodinSourceIndexMap_value {α θ : V} (hα : α ∈ θ) :
    (woodinSourceIndexMap θ) ‘ α = woodinSourceIndex α := value_definableGraph _ _ _ hα

theorem woodinRecursiveIndexMap_value {β θ : V} (hβ : β ∈ woodinSourceIndices θ) :
    (woodinRecursiveIndexMap θ) ‘ β = woodinRecursiveIndex β := value_definableGraph _ _ _ hβ

theorem woodinSourceIndexMap_left_inverse {α θ : V} [IsOrdinal θ] (hα : α ∈ θ) :
    (woodinRecursiveIndexMap θ) ‘ ((woodinSourceIndexMap θ) ‘ α) = α := by
  let := IsOrdinal.of_mem hα
  rw [woodinSourceIndexMap_value hα,
    woodinRecursiveIndexMap_value (woodinSourceIndex_mem_indices hα), woodinRecursiveIndex_sourceIndex]

theorem woodinSourceIndexMap_right_inverse {β θ : V} [IsOrdinal θ]
    (hβ : β ∈ woodinSourceIndices θ) :
    (woodinSourceIndexMap θ) ‘ ((woodinRecursiveIndexMap θ) ‘ β) = β := by
  have hh := mem_woodinSourceIndices.mp hβ
  let := IsOrdinal.of_mem hh.1
  rw [woodinRecursiveIndexMap_value hβ,
    woodinSourceIndexMap_value (woodinRecursiveIndex_mem_of_indices hβ),
    woodinSourceIndex_recursiveIndex β hh.2]

end ZFVP
