import ZFVP.ModelTheory.SuccessorLowNameValues

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V W : Type*} [SetStructure V] [SetStructure W]
  [Nonempty V] [Nonempty W] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [W↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace ForcingRealization
variable {A : ForcingContext V} (L : ForcingRealization A W)

theorem low_nameValues_eq_hierarchy {η : V} [IsOrdinal η]
    (hlow : ∀ x ∈ hierarchy (L.ground η), ∃ σ ∈ lowRankNameSet A.P η,
      x = nameValue L.genericSet (L.ground σ)) :
    L.nameValues (lowRankNameSet A.P η) = hierarchy (L.ground η) := by
  apply SetTheory.subset_antisymm (L.low_nameValues_subset_hierarchy η)
  exact fun x hx ↦ L.mem_nameValues.mpr (hlow x hx)

theorem successor_low_nameValues_eq_hierarchy {η : V} [IsOrdinal η]
    (hlow : ∀ x ∈ hierarchy (L.ground η), ∃ σ ∈ lowRankNameSet A.P η,
      x = nameValue L.genericSet (L.ground σ))
    (hrep : ∀ x ∈ hierarchy (succ (L.ground η)), ∃ τ : ForcingName A.P,
      x = nameValue L.genericSet (L.ground τ.val)) :
    L.nameValues (successorLowNameSet A.P η) = hierarchy (succ (L.ground η)) := by
  let := (L.ground.ordinal_iff η).mpr inferInstance
  apply mem_ext
  intro x
  rw [L.mem_successor_low_nameValues_iff, L.low_nameValues_eq_hierarchy hlow,
    hierarchy_succ, mem_power_iff]
  constructor
  · exact And.left
  · intro hx
    exact ⟨hx, hrep x (by rwa [hierarchy_succ, mem_power_iff])⟩

theorem successor_low_nameValues_eq_hierarchy_of_surjective {η : V} [IsOrdinal η]
    (hlow : ∀ x ∈ hierarchy (L.ground η), ∃ σ ∈ lowRankNameSet A.P η,
      x = nameValue L.genericSet (L.ground σ))
    (honto : Function.Surjective L.value) :
    L.nameValues (successorLowNameSet A.P η) = hierarchy (succ (L.ground η)) := by
  apply L.successor_low_nameValues_eq_hierarchy hlow
  intro x _
  obtain ⟨y, rfl⟩ := honto x
  obtain ⟨τ, rfl⟩ := A.ofName_surjective y
  exact ⟨τ, L.value_ofName τ⟩

end ForcingRealization

namespace ForcingContext
variable (A : ForcingContext V)

theorem successor_low_name_coverage {η : V} [IsOrdinal η]
    (hlow : ∀ x ∈ hierarchy (A.check η), ∃ σ : ForcingName A.P,
      σ.val ∈ hierarchy η ∧ x = A.ofName σ) (x : A.Model) :
    x ∈ hierarchy (succ (A.check η)) ↔ ∃ τ : ForcingName A.P,
      τ.val ∈ successorLowNameSet A.P η ∧ x = A.ofName τ := by
  have hcov : ∀ y ∈ hierarchy (A.realization.ground η),
      ∃ σ ∈ lowRankNameSet A.P η,
        y = nameValue A.realization.genericSet (A.realization.ground σ) := by
    intro y hy
    obtain ⟨σ, hσ, rfl⟩ := hlow y hy
    refine ⟨σ.val, (mem_lowRankNameSet _ _ _).mpr ⟨hσ, σ.property⟩, ?_⟩
    rw [← A.realization.value_ofName, A.realization_value]
  have honto : Function.Surjective A.realization.value :=
    fun y ↦ ⟨y, A.realization_value y⟩
  have he := A.realization.successor_low_nameValues_eq_hierarchy_of_surjective hcov honto
  change x ∈ hierarchy (succ (A.realization.ground η)) ↔ _
  rw [← he, A.realization.mem_nameValues]
  constructor
  · rintro ⟨τ, hτ, hx⟩
    let t : ForcingName A.P := ⟨τ, successorLowNameSet_isName hτ⟩
    refine ⟨t, hτ, ?_⟩
    rw [← A.realization.value_ofName t, A.realization_value] at hx
    exact hx
  · rintro ⟨τ, hτ, hx⟩
    refine ⟨τ.val, hτ, ?_⟩
    rw [← A.realization.value_ofName τ, A.realization_value]
    exact hx

end ForcingContext
end ZFVP
