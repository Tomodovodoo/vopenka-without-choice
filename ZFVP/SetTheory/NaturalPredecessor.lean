import ZFVP.SetTheory.StandardNaturals
import Foundation.FirstOrder.SetTheory.Ordinal

/-! Predecessors and index shifts for internal natural numbers. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem internalNatural_cases {n : V} (hn : n ∈ (ω : V)) :
    n = 0 ∨ ∃ i ∈ (ω : V), n = succ i := by
  apply naturalNumber_induction (fun n ↦ n = 0 ∨ ∃ i ∈ (ω : V), n = succ i)
    (by definability) (Or.inl rfl) ?_ n hn
  intro i hi _
  exact Or.inr ⟨i, hi, rfl⟩

theorem sUnion_succ_of_transitive (n : V) [IsTransitive n] : ⋃ˢ (succ n) = n := by
  apply mem_ext
  intro i
  constructor
  · intro hi
    obtain ⟨j, hj, hij⟩ := mem_sUnion_iff.mp hi
    rcases mem_succ_iff.mp hj with rfl | hj
    · exact hij
    · exact (inferInstance : IsTransitive n).mem_trans hij hj
  · intro hi
    exact mem_sUnion_iff.mpr ⟨n, by simp, hi⟩

theorem zero_mem_succ_natural {n : V} (hn : n ∈ (ω : V)) : (0 : V) ∈ succ n := by
  have : IsOrdinal n := IsOrdinal.of_mem hn
  rcases IsOrdinal.subset_iff.mp (empty_subset n) with heq | hlt
  · rw [← heq]
    simp [zero_def]
  · exact mem_succ_iff.mpr (Or.inr hlt)

theorem natural_predecessor_mem {n i : V} (hn : n ∈ (ω : V))
    (hi : i ∈ succ n) (hne : i ≠ 0) : ⋃ˢ i ∈ n := by
  have hiω : i ∈ (ω : V) := IsOrdinal.toIsTransitive.mem_trans hi (ω_succ_closed hn)
  rcases internalNatural_cases hiω with hzero | ⟨j, hj, rfl⟩
  · exact False.elim (hne hzero)
  · have : IsOrdinal j := IsOrdinal.of_mem hj
    rw [sUnion_succ_of_transitive]
    rcases mem_succ_iff.mp hi with heq | hlt
    · rw [← heq]
      simp
    · have : IsOrdinal n := IsOrdinal.of_mem hn
      exact IsOrdinal.toIsTransitive.mem_trans (by simp : j ∈ succ j) hlt

theorem succ_mem_succ_of_natural_mem {n i : V} (hn : n ∈ (ω : V)) (hi : i ∈ n) :
    succ i ∈ succ n := by
  have : IsOrdinal n := IsOrdinal.of_mem hn
  have : IsOrdinal i := IsOrdinal.of_mem hi
  have hsub : succ i ⊆ n := by
    intro j hj
    rcases mem_succ_iff.mp hj with rfl | hj
    · exact hi
    · exact IsOrdinal.toIsTransitive.mem_trans hj hi
  exact mem_succ_iff.mpr (IsOrdinal.subset_iff.mp hsub)

end ZFVP

