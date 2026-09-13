import ZFVP.SetTheory.StationarySets

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def unboundedInFormula : SetTheorySemisentence 2 :=
  “C κ. C ⊆ κ ∧ ∀ ξ ∈ κ, ∃ η ∈ C, ξ ∈ η”

def closedInFormula : SetTheorySemisentence 2 :=
  “C κ. C ⊆ κ ∧ ∀ δ ∈ κ, ¬!isEmpty δ → (∀ ξ ∈ δ, ∃ η ∈ C, η ∈ δ ∧ ξ ∈ η) → δ ∈ C”

def clubInFormula : SetTheorySemisentence 2 := “C κ. !closedInFormula C κ ∧ !unboundedInFormula C κ”

def stationaryInFormula : SetTheorySemisentence 2 :=
  “S κ. S ⊆ κ ∧ ∀ C, !clubInFormula C κ → ∃ δ ∈ S, δ ∈ C”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

instance unboundedInFormula_defined : ℒₛₑₜ-relation[V] IsUnboundedIn via unboundedInFormula :=
  ⟨fun v ↦ by simp [unboundedInFormula, IsUnboundedIn]⟩

instance closedInFormula_defined : ℒₛₑₜ-relation[V] IsClosedIn via closedInFormula :=
  ⟨fun v ↦ by simp [closedInFormula, IsClosedIn, isEmpty_iff_eq_empty, zero_def]⟩

instance clubInFormula_defined : ℒₛₑₜ-relation[V] IsClubIn via clubInFormula :=
  ⟨fun v ↦ by simp [clubInFormula, IsClubIn]⟩

instance stationaryInFormula_defined : ℒₛₑₜ-relation[V] IsStationaryIn via stationaryInFormula :=
  ⟨fun v ↦ by simp [stationaryInFormula, IsStationaryIn]⟩

namespace ElementaryMap

variable {W : Type*} [SetStructure W] [Nonempty W] [W↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

omit [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [Nonempty W] [W↓[ℒₛₑₜ] ⊧* 𝗭𝗙] in
theorem map_unboundedIn_iff (j : ElementaryMap V W) (C κ : V) :
    IsUnboundedIn (j C) (j κ) ↔ IsUnboundedIn C κ :=
  (j.map_defined unboundedInFormula (fun v ↦ IsUnboundedIn (v 0) (v 1))
    (fun v ↦ IsUnboundedIn (v 0) (v 1)) ![C, κ]).symm

theorem map_closedIn_iff (j : ElementaryMap V W) (C κ : V) :
    IsClosedIn (j C) (j κ) ↔ IsClosedIn C κ :=
  (j.map_defined closedInFormula (fun v ↦ IsClosedIn (v 0) (v 1))
    (fun v ↦ IsClosedIn (v 0) (v 1)) ![C, κ]).symm

theorem map_clubIn_iff (j : ElementaryMap V W) (C κ : V) :
    IsClubIn (j C) (j κ) ↔ IsClubIn C κ :=
  (j.map_defined clubInFormula (fun v ↦ IsClubIn (v 0) (v 1))
    (fun v ↦ IsClubIn (v 0) (v 1)) ![C, κ]).symm

theorem map_stationaryIn_iff (j : ElementaryMap V W) (S κ : V) :
    IsStationaryIn (j S) (j κ) ↔ IsStationaryIn S κ :=
  (j.map_defined stationaryInFormula (fun v ↦ IsStationaryIn (v 0) (v 1))
    (fun v ↦ IsStationaryIn (v 0) (v 1)) ![S, κ]).symm

end ElementaryMap
end ZFVP
