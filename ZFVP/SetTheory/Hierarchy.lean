import ZFVP.SetTheory.DefinableGraph
import Foundation.FirstOrder.SetTheory.Recursion

/-! The cumulative hierarchy constructed by internal ordinal recursion.
All stages and the recursion graphs are sets of the given ZF model.
-/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- Union of the power sets of the earlier stages recorded by `f`. -/
noncomputable def hierarchyStep (f : V) : V :=
  ⋃ˢ repl (fun x ↦ ℘ x) (by definability) (range f)

instance hierarchyStep_definable : ℒₛₑₜ-function₁[V] hierarchyStep := by
  unfold hierarchyStep
  definability

/-- The internal cumulative stage V_alpha. Values outside the ordinals are empty. -/
noncomputable def hierarchy (α : V) : V :=
  Replacement.transfiniteRec hierarchyStep hierarchyStep_definable α

instance hierarchy_definable : ℒₛₑₜ-function₁[V] hierarchy :=
  Replacement.transfiniteRec_definable hierarchyStep_definable

theorem hierarchy_recursion (α : Ordinal V) :
    hierarchy (α : V) = hierarchyStep
      (definableGraph (α : V) hierarchy hierarchy_definable) := by
  exact Replacement.transfiniteRec_spec hierarchyStep hierarchyStep_definable α

theorem mem_hierarchyStep_iff (f x : V) :
    x ∈ hierarchyStep f ↔ ∃ y ∈ range f, x ⊆ y := by
  simp only [hierarchyStep, mem_sUnion_iff, repl_spec]
  constructor
  · rintro ⟨p, ⟨y, hy, rfl⟩, hx⟩
    exact ⟨y, hy, by simpa using hx⟩
  · rintro ⟨y, hy, hx⟩
    exact ⟨℘ y, ⟨y, hy, rfl⟩, by simpa using hx⟩

theorem mem_hierarchy_iff (α : Ordinal V) (x : V) :
    x ∈ hierarchy (α : V) ↔ ∃ β ∈ (α : V), x ⊆ hierarchy β := by
  rw [hierarchy_recursion, mem_hierarchyStep_iff, range_definableGraph]
  simp only [repl_spec]
  constructor
  · rintro ⟨y, ⟨β, hβ, rfl⟩, hx⟩
    exact ⟨β, hβ, hx⟩
  · rintro ⟨β, hβ, hx⟩
    exact ⟨hierarchy β, ⟨β, hβ, rfl⟩, hx⟩

theorem mem_hierarchy_iff_of_ordinal (α : V) [IsOrdinal α] (x : V) :
    x ∈ hierarchy α ↔ ∃ β ∈ α, x ⊆ hierarchy β :=
  mem_hierarchy_iff (IsOrdinal.toOrdinal α) x

theorem hierarchy_empty : hierarchy (∅ : V) = ∅ := by
  ext x
  rw [mem_hierarchy_iff_of_ordinal]
  simp

theorem hierarchy_mono {α β : V} [IsOrdinal α] [IsOrdinal β]
    (h : α ⊆ β) : hierarchy α ⊆ hierarchy β := by
  intro x hx
  obtain ⟨γ, hγα, hxγ⟩ := (mem_hierarchy_iff (IsOrdinal.toOrdinal α) x).mp hx
  exact (mem_hierarchy_iff (IsOrdinal.toOrdinal β) x).mpr ⟨γ, h γ hγα, hxγ⟩

theorem hierarchy_mem {α β : V} [IsOrdinal β] (h : α ∈ β) :
    hierarchy α ∈ hierarchy β := by
  exact (mem_hierarchy_iff (IsOrdinal.toOrdinal β) (hierarchy α)).mpr
    ⟨α, h, subset_refl _⟩

theorem hierarchy_transitive (α : V) [IsOrdinal α] : IsTransitive (hierarchy α) := by
  constructor
  intro x hx z hz
  obtain ⟨β, hβα, hxβ⟩ := (mem_hierarchy_iff (IsOrdinal.toOrdinal α) x).mp hx
  have : IsOrdinal β := IsOrdinal.of_mem hβα
  exact hierarchy_mono (IsOrdinal.toIsTransitive.transitive β hβα) z (hxβ z hz)

theorem hierarchy_succ (α : V) [IsOrdinal α] : hierarchy (succ α) = ℘ (hierarchy α) := by
  ext x
  rw [mem_hierarchy_iff_of_ordinal, mem_power_iff]
  constructor
  · rintro ⟨β, hβ, hxβ⟩
    rcases mem_succ_iff.mp hβ with rfl | hβα
    · exact hxβ
    · have : IsOrdinal β := IsOrdinal.of_mem hβα
      exact subset_trans hxβ (hierarchy_mono (IsOrdinal.toIsTransitive.transitive β hβα))
  · intro hx
    exact ⟨α, by simp, hx⟩

theorem hierarchy_limit (α : V) [IsOrdinal α]
    (closed : ∀ β ∈ α, succ β ∈ α) (x : V) :
    x ∈ hierarchy α ↔ ∃ β ∈ α, x ∈ hierarchy β := by
  constructor
  · intro hx
    obtain ⟨β, hβα, hxβ⟩ := (mem_hierarchy_iff (IsOrdinal.toOrdinal α) x).mp hx
    have : IsOrdinal β := IsOrdinal.of_mem hβα
    refine ⟨succ β, closed β hβα, ?_⟩
    rw [hierarchy_succ, mem_power_iff]
    exact hxβ
  · rintro ⟨β, hβα, hxβ⟩
    have : IsOrdinal β := IsOrdinal.of_mem hβα
    exact hierarchy_mono (IsOrdinal.toIsTransitive.transitive β hβα) x hxβ

end ZFVP
