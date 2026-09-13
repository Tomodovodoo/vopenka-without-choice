import ZFVP.SetTheory.LeastRankWitnesses
import ZFVP.SetTheory.UniformRank

/-! Uniform formulas for least-rank witness sets. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def leastWitnessRankFormula (φ : SetTheorySemisentence 2) : SetTheorySemisentence 2 :=
  f“x α. !IsOrdinal.dfn α ∧ (∃ y, !φ x y ∧ !rankFormula y = α) ∧
    ∀ β, !IsOrdinal.dfn β → (∃ y, !φ x y ∧ !rankFormula y = β) → α ⊆ β”

def leastRankWitnessSetFormula (φ : SetTheorySemisentence 2) : SetTheorySemisentence 2 :=
  f“x X. ∃ α, !(leastWitnessRankFormula φ) x α ∧
    ∀ y, y ∈ X ↔ !φ x y ∧ !rankFormula y = α”

variable {V W : Type*} [SetStructure V] [SetStructure W]
  [Nonempty V] [Nonempty W] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [W↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

instance leastWitnessRankFormula_defined (R : V → V → Prop)
    (φ : SetTheorySemisentence 2) [ℒₛₑₜ-relation R via φ] :
    ℒₛₑₜ-relation (IsLeastWitnessRank R) via leastWitnessRankFormula φ :=
  ⟨fun v ↦ by simp [leastWitnessRankFormula, IsLeastWitnessRank, IsLeastOrdinal]⟩

instance leastRankWitnessSetFormula_defined (R : V → V → Prop)
    (φ : SetTheorySemisentence 2) [ℒₛₑₜ-relation R via φ] :
    ℒₛₑₜ-relation (IsLeastRankWitnessSet R) via leastRankWitnessSetFormula φ :=
  ⟨fun v ↦ by simp [leastRankWitnessSetFormula, IsLeastRankWitnessSet]⟩

theorem ElementaryMap.map_leastRankWitnessSet_iff (j : ElementaryMap V W)
    (φ : SetTheorySemisentence 2) (R : V → V → Prop) (S : W → W → Prop)
    [ℒₛₑₜ-relation R via φ] [ℒₛₑₜ-relation S via φ] (x X : V) :
    IsLeastRankWitnessSet S (j x) (j X) ↔ IsLeastRankWitnessSet R x X :=
  (j.map_defined (leastRankWitnessSetFormula φ)
    (fun v ↦ IsLeastRankWitnessSet R (v 0) (v 1))
    (fun v ↦ IsLeastRankWitnessSet S (v 0) (v 1)) ![x, X]).symm

end ZFVP
