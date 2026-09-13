import ZFVP.SetTheory.SetCollapse
import ZFVP.SetTheory.RankBounds

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- An internally finite subset of a nonzero limit rank belongs to that rank. -/
theorem internallyFinite_mem_hierarchy_limit {κ A : V} [IsOrdinal κ]
    (hκ : ∀ β ∈ κ, succ β ∈ κ) (hzero : (∅ : V) ∈ κ)
    (hA : IsInternallyFinite A) (hsub : A ⊆ hierarchy κ) : A ∈ hierarchy κ := by
  apply internallyFinite_induction (fun A ↦ A ⊆ hierarchy κ → A ∈ hierarchy κ)
    (by definability) ?_ ?_ A hA hsub
  · intro _
    exact ordinal_subset_hierarchy κ ∅ hzero
  · intro B b ih hB
    have hb : b ∈ hierarchy κ := hB b (mem_insert.mpr (Or.inl rfl))
    have hBV : B ∈ hierarchy κ := ih (fun z hz ↦ hB z (mem_insert.mpr (Or.inr hz)))
    obtain ⟨β, hβ, hBβ, hbβ⟩ := common_hierarchy_stage hκ hBV hb
    have : IsOrdinal β := IsOrdinal.of_mem hβ
    apply mem_hierarchy_of_mem_stage (hκ β hβ)
    rw [hierarchy_succ, mem_power_iff]
    intro z hz
    rcases mem_insert.mp hz with rfl | hz
    · exact hbβ
    · exact (hierarchy_transitive β).mem_trans hz hBβ

/-- Every finite partial collapse condition over `Vκ` belongs to `Vκ`. -/
theorem collapseConditions_subset_hierarchy {κ : V} [IsOrdinal κ]
    (hω : (ω : V) ∈ κ) (hκ : ∀ β ∈ κ, succ β ∈ κ) :
    collapseConditions (hierarchy κ) ⊆ hierarchy κ := by
  intro p hp
  obtain ⟨hpSub, hpf, hpFin⟩ := (mem_finitePartialFunctions ω (hierarchy κ) p).mp hp
  have : IsFunction p := hpf
  apply internallyFinite_mem_hierarchy_limit hκ
    (IsOrdinal.toIsTransitive.mem_trans empty_mem_ω hω) (internallyFinite_function hpFin)
  intro q hq
  obtain ⟨n, hn, y, hy, rfl⟩ := mem_prod_iff.mp (hpSub q hq)
  have hnκ : n ∈ κ := IsOrdinal.toIsTransitive.mem_trans hn hω
  exact kpair_mem_hierarchy_limit hκ (ordinal_subset_hierarchy κ n hnκ) hy

end ZFVP

