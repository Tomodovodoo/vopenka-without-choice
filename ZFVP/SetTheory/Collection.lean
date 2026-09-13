import ZFVP.SetTheory.Rank

/-! Collection in internal ZF, obtained by bounding least witness stages.
No function choosing one witness for each input is used. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

def IsLeastWitnessStage (R : V → V → Prop) (x α : V) : Prop :=
  IsLeastOrdinal (fun β ↦ ∃ y ∈ hierarchy β, R x y) α

theorem isLeastWitnessStage_definable (R : V → V → Prop) (hR : ℒₛₑₜ-relation R) :
    ℒₛₑₜ-relation (IsLeastWitnessStage R) := by
  unfold IsLeastWitnessStage IsLeastOrdinal
  definability

theorem leastWitnessStage_existsUnique (R : V → V → Prop) (hR : ℒₛₑₜ-relation R)
    (x : V) (hex : ∃ y, R x y) : ∃! α, IsLeastWitnessStage R x α := by
  obtain ⟨y, hy⟩ := hex
  apply leastOrdinal_existsUnique _ (by definability)
  refine ⟨succ (rank y), inferInstance, y, ?_, hy⟩
  rw [hierarchy_succ, mem_power_iff]
  exact subset_hierarchy_rank y

/-- The ZF Collection scheme for an arbitrary definable relation. -/
theorem collection (A : V) (R : V → V → Prop) (hR : ℒₛₑₜ-relation R)
    (h : ∀ x ∈ A, ∃ y, R x y) : ∃ B : V, ∀ x ∈ A, ∃ y ∈ B, R x y := by
  have hw : ∀ x ∈ A, ∃! α, IsLeastWitnessStage R x α :=
    fun x hx ↦ leastWitnessStage_existsUnique R hR x (h x hx)
  obtain ⟨C, hC⟩ := replacement_rel_exists_of_mem_existsUnique A
    (IsLeastWitnessStage R) hw (isLeastWitnessStage_definable R hR)
  have hκ : IsOrdinal (⋃ˢ C) := IsOrdinal.sUnion (by
    intro α hα
    obtain ⟨x, _, hx⟩ := (hC α).mp hα
    exact hx.1)
  refine ⟨hierarchy (⋃ˢ C), ?_⟩
  intro x hx
  obtain ⟨α, hα, _⟩ := hw x hx
  obtain ⟨y, hy, hRxy⟩ := hα.2.1
  have : IsOrdinal α := hα.1
  have hαC : α ∈ C := (hC α).mpr ⟨x, hx, hα⟩
  exact ⟨y, hierarchy_mono (subset_sUnion_of_mem hαC) y hy, hRxy⟩

/-- Collection with no irrelevant elements in the collecting set. -/
theorem strongCollection (A : V) (R : V → V → Prop) (hR : ℒₛₑₜ-relation R)
    (h : ∀ x ∈ A, ∃ y, R x y) :
    ∃ B : V, (∀ x ∈ A, ∃ y ∈ B, R x y) ∧ ∀ y ∈ B, ∃ x ∈ A, R x y := by
  obtain ⟨C, hC⟩ := collection A R hR h
  refine ⟨{y ∈ C ; ∃ x ∈ A, R x y}, ?_, ?_⟩
  · intro x hx
    obtain ⟨y, hy, hxy⟩ := hC x hx
    exact ⟨y, by simp [hy]; exact ⟨x, hx, hxy⟩, hxy⟩
  · intro y hy
    simpa using (show y ∈ C ∧ ∃ x ∈ A, R x y from by simpa using hy).2

end ZFVP
