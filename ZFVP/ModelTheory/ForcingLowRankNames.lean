import ZFVP.SetTheory.ForcingNameHierarchyCn
import ZFVP.ModelTheory.ForcingHierarchyEvaluation
import ZFVP.ModelTheory.ForcingModelRank
import ZFVP.SetTheory.ForcingNameHierarchyBound

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace ForcingContext

theorem ofName_mem_checked_hierarchy (A : ForcingContext V) {δ : V} [IsOrdinal δ]
    (τ : ForcingName A.P) (hτ : τ.val ∈ hierarchy δ) :
    A.ofName τ ∈ hierarchy (A.check δ) := by
  have hb := A.rank_ofName_subset τ
  have hr : A.check (rank τ.val) ∈ A.check δ :=
    (A.check_mem_iff _ _).mpr ((mem_hierarchy_iff_rank_mem _ _).mp hτ)
  apply (mem_hierarchy_iff_rank_mem _ _).mpr
  rcases IsOrdinal.subset_iff.mp hb with he | hm
  · exact he.symm ▸ hr
  · exact IsOrdinal.toIsTransitive.mem_trans hm hr

theorem mem_checked_hierarchy_iff_low_name (A : ForcingContext V) {δ : V}
    (hδ : Cn 1 δ) (hP : A.P ∈ hierarchy δ) (x : A.Model) :
    x ∈ hierarchy (A.check δ) ↔
      ∃ τ : ForcingName A.P, τ.val ∈ hierarchy δ ∧ x = A.ofName τ := by
  let := hδ.ordinal
  constructor
  · intro hx
    rw [← A.hierarchyName_value δ] at hx
    obtain ⟨τ, hτ, rfl⟩ := (A.mem_hierarchyName_iff δ x).mp hx
    obtain ⟨β, hβ, hb⟩ := (mem_forcingNameHierarchy A.P δ τ.val).mp hτ
    let := IsOrdinal.of_mem hβ
    have ht : τ.val ∈ forcingNameHierarchy A.P (succ β) := by
      rw [forcingNameHierarchy_succ, mem_power_iff]
      exact hb
    exact ⟨τ, (hierarchy_transitive δ).mem_trans ht
      (hδ.forcingNameHierarchy_closed hP (hδ.successor_closed _ hβ)), rfl⟩
  · rintro ⟨τ, hτ, rfl⟩
    exact A.ofName_mem_checked_hierarchy τ hτ

theorem mem_checked_hierarchy_iff_low_name_of_inaccessible (A : ForcingContext V) {δ : V}
    (hδ : IsChoicelessInaccessible δ) (hP : A.P ∈ hierarchy δ) (x : A.Model) :
    x ∈ hierarchy (A.check δ) ↔
      ∃ τ : ForcingName A.P, τ.val ∈ hierarchy δ ∧ x = A.ofName τ := by
  let := hδ.1
  constructor
  · intro hx
    rw [← A.hierarchyName_value δ] at hx
    obtain ⟨τ, hτ, rfl⟩ := (A.mem_hierarchyName_iff δ x).mp hx
    obtain ⟨β, hβ, hb⟩ := (mem_forcingNameHierarchy A.P δ τ.val).mp hτ
    let := IsOrdinal.of_mem hβ
    have ht : τ.val ∈ forcingNameHierarchy A.P (succ β) := by
      rw [forcingNameHierarchy_succ, mem_power_iff]
      exact hb
    exact ⟨τ, (hierarchy_transitive δ).mem_trans ht
      (forcingNameHierarchy_mem_hierarchy hδ hP (regularCardinal_succ_closed hδ.regular hβ)), rfl⟩
  · rintro ⟨τ, hτ, rfl⟩
    exact A.ofName_mem_checked_hierarchy τ hτ

end ForcingContext
end ZFVP
