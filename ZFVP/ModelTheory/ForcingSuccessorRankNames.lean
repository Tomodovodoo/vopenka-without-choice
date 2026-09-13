import ZFVP.ModelTheory.ForcingLowRankNames

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem Cn.forcingNameHierarchy_subset {δ P : V} (hδ : Cn 1 δ)
    (hP : P ∈ hierarchy δ) : forcingNameHierarchy P δ ⊆ hierarchy δ := by
  let := hδ.ordinal
  intro τ hτ
  obtain ⟨β, hβ, hb⟩ := (mem_forcingNameHierarchy P δ τ).mp hτ
  let := IsOrdinal.of_mem hβ
  have ht : τ ∈ forcingNameHierarchy P (succ β) := by
    rw [forcingNameHierarchy_succ, mem_power_iff]
    exact hb
  exact (hierarchy_transitive δ).mem_trans ht
    (hδ.forcingNameHierarchy_closed hP (hδ.successor_closed _ hβ))

theorem Cn.forcingNameHierarchy_successor_subset {δ P : V} (hδ : Cn 1 δ)
    (hP : P ∈ hierarchy δ) : forcingNameHierarchy P (succ δ) ⊆ hierarchy (succ δ) := by
  let := hδ.ordinal
  intro τ hτ
  rw [forcingNameHierarchy_succ, mem_power_iff] at hτ
  rw [hierarchy_succ, mem_power_iff]
  intro z hz
  obtain ⟨σ, hσ, p, hp, rfl⟩ := mem_prod_iff.mp (hτ z hz)
  exact kpair_mem_hierarchy_limit hδ.successor_closed (hδ.forcingNameHierarchy_subset hP σ hσ)
    ((hierarchy_transitive δ).mem_trans hp hP)

namespace ForcingContext

theorem mem_checked_successorHierarchy_iff_name (A : ForcingContext V) {δ : V}
    (hδ : Cn 1 δ) (hP : A.P ∈ hierarchy δ) (x : A.Model) :
    x ∈ hierarchy (A.check (succ δ)) ↔
      ∃ τ : ForcingName A.P, τ.val ∈ hierarchy (succ δ) ∧ x = A.ofName τ := by
  let := hδ.ordinal
  constructor
  · intro hx
    rw [← A.hierarchyName_value (succ δ)] at hx
    obtain ⟨τ, hτ, he⟩ := (A.mem_hierarchyName_iff (succ δ) x).mp hx
    exact ⟨τ, hδ.forcingNameHierarchy_successor_subset hP τ.val hτ, he⟩
  · rintro ⟨τ, hτ, rfl⟩
    exact A.ofName_mem_checked_hierarchy τ hτ

end ForcingContext
end ZFVP
