import ZFVP.SetTheory.Collection

/-! Scott's least-rank witness sets in internal ZF. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

def IsLeastWitnessRank (R : V → V → Prop) (x α : V) : Prop :=
  IsLeastOrdinal (fun β ↦ ∃ y, R x y ∧ rank y = β) α

theorem isLeastWitnessRank_definable (R : V → V → Prop) (hR : ℒₛₑₜ-relation R) :
    ℒₛₑₜ-relation (IsLeastWitnessRank R) := by
  unfold IsLeastWitnessRank IsLeastOrdinal
  definability

theorem leastWitnessRank_existsUnique (R : V → V → Prop) (hR : ℒₛₑₜ-relation R)
    (x : V) (hex : ∃ y, R x y) : ∃! α, IsLeastWitnessRank R x α := by
  obtain ⟨y, hy⟩ := hex
  exact leastOrdinal_existsUnique _ (by definability)
    ⟨rank y, inferInstance, y, hy, rfl⟩

/-- The full set of witnesses of the least possible rank. -/
def IsLeastRankWitnessSet (R : V → V → Prop) (x X : V) : Prop :=
  ∃ α, IsLeastWitnessRank R x α ∧ ∀ y, y ∈ X ↔ R x y ∧ rank y = α

theorem isLeastRankWitnessSet_definable (R : V → V → Prop) (hR : ℒₛₑₜ-relation R) :
    ℒₛₑₜ-relation (IsLeastRankWitnessSet R) := by
  have := isLeastWitnessRank_definable R hR
  unfold IsLeastRankWitnessSet
  definability

theorem leastRankWitnessSet_existsUnique (R : V → V → Prop) (hR : ℒₛₑₜ-relation R)
    (x : V) (hex : ∃ y, R x y) : ∃! X, IsLeastRankWitnessSet R x X := by
  obtain ⟨α, hα, huniq⟩ := leastWitnessRank_existsUnique R hR x hex
  have : IsOrdinal α := hα.1
  let X : V := {y ∈ hierarchy (succ α) ; R x y ∧ rank y = α}
  have hX : ∀ y, y ∈ X ↔ R x y ∧ rank y = α := by
    intro y
    constructor
    · intro hy
      exact (show y ∈ hierarchy (succ α) ∧ R x y ∧ rank y = α from by
        simpa [X] using hy).2
    · intro hy
      have hb : y ∈ hierarchy (succ α) := by
        rw [mem_hierarchy_iff_rank_mem, hy.2]
        simp
      simpa [X, hb] using hy
  refine ⟨X, ⟨α, hα, hX⟩, ?_⟩
  rintro Y ⟨β, hβ, hY⟩
  have heq : β = α := huniq β hβ
  apply mem_ext
  intro y
  rw [hY, hX, heq]

theorem IsLeastRankWitnessSet.nonempty {R : V → V → Prop} {x X : V}
    (hX : IsLeastRankWitnessSet R x X) : IsNonempty X := by
  obtain ⟨α, hα, hmem⟩ := hX
  obtain ⟨y, hy, hr⟩ := hα.2.1
  exact ⟨y, (hmem y).mpr ⟨hy, hr⟩⟩

theorem IsLeastRankWitnessSet.witness {R : V → V → Prop} {x X y : V}
    (hX : IsLeastRankWitnessSet R x X) (hy : y ∈ X) : R x y := by
  obtain ⟨α, _, hmem⟩ := hX
  exact ((hmem y).mp hy).1

theorem IsLeastRankWitnessSet.rank_minimal {R : V → V → Prop} {x X y z : V}
    (hX : IsLeastRankWitnessSet R x X) (hy : y ∈ X) (hz : R x z) :
    rank y ⊆ rank z := by
  obtain ⟨α, hα, hmem⟩ := hX
  rw [((hmem y).mp hy).2]
  exact hα.2.2 (rank z) inferInstance ⟨z, hz, rfl⟩

/-- Replacement collects the uniquely specified witness sets, without selecting
a member of any witness set. -/
theorem leastRankWitnessSets_collect (A : V) (R : V → V → Prop)
    (hR : ℒₛₑₜ-relation R) (h : ∀ x ∈ A, ∃ y, R x y) :
    ∃ B : V, ∀ X, X ∈ B ↔ ∃ x ∈ A, IsLeastRankWitnessSet R x X :=
  replacement_rel_exists_of_mem_existsUnique A (IsLeastRankWitnessSet R)
    (fun x hx ↦ leastRankWitnessSet_existsUnique R hR x (h x hx))
    (isLeastRankWitnessSet_definable R hR)

end ZFVP
