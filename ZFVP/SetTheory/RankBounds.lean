import ZFVP.SetTheory.Rank
import ZFVP.SetTheory.OrdinalAddition

/-! Rank closure bounds for later set-coded syntax and satisfaction. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem ordinal_subset_hierarchy (α : V) [IsOrdinal α] : α ⊆ hierarchy α := by
  apply transfinite_induction (P := fun β : V ↦ β ⊆ hierarchy β)
    (by definability) ?_ (IsOrdinal.toOrdinal α)
  intro β ih x hx
  have : IsOrdinal x := IsOrdinal.of_mem hx
  exact (mem_hierarchy_iff β x).mpr ⟨x, hx, ih (IsOrdinal.toOrdinal x) hx⟩

theorem rank_of_ordinal (α : V) [IsOrdinal α] : rank α = α := by
  apply transfinite_induction (P := fun β : V ↦ rank β = β)
    (by definability) ?_ (IsOrdinal.toOrdinal α)
  intro β ih
  have hs := rank_minimal (β : V) β β.ordinal (ordinal_subset_hierarchy (β : V))
  rcases IsOrdinal.subset_iff.mp hs with heq | hlt
  · exact heq
  · have hi := ih (IsOrdinal.toOrdinal (rank (β : V))) hlt
    change rank (rank (β : V)) = rank (β : V) at hi
    have hb := rank_mem hlt
    rw [hi] at hb
    exact False.elim (mem_irrefl _ hb)

theorem rank_singleton (x : V) : rank ({x} : V) = succ (rank x) := by
  apply SetTheory.subset_antisymm
  · apply rank_minimal _ _ inferInstance
    intro y hy
    have heq : y = x := by simpa using hy
    rw [heq, mem_hierarchy_iff_rank_mem]
    simp
  · have hx : rank x ∈ rank ({x} : V) := rank_mem (by simp)
    intro β hβ
    rcases mem_succ_iff.mp hβ with rfl | hβ
    · exact hx
    · exact IsOrdinal.toIsTransitive.mem_trans hβ hx

theorem pair_subset_hierarchy {α x y : V} [IsOrdinal α]
    (hx : x ∈ hierarchy α) (hy : y ∈ hierarchy α) : ({x, y} : V) ⊆ hierarchy α := by
  intro z hz
  rcases show z = x ∨ z = y from by simpa using hz with rfl | rfl
  · exact hx
  · exact hy

theorem pair_mem_hierarchy_succ {α x y : V} [IsOrdinal α]
    (hx : x ∈ hierarchy α) (hy : y ∈ hierarchy α) : ({x, y} : V) ∈ hierarchy (succ α) := by
  rw [hierarchy_succ, mem_power_iff]
  exact pair_subset_hierarchy hx hy

theorem kpair_mem_hierarchy_succ_succ {α x y : V} [IsOrdinal α]
    (hx : x ∈ hierarchy α) (hy : y ∈ hierarchy α) :
    ⟨x, y⟩ₖ ∈ hierarchy (succ (succ α)) := by
  apply pair_mem_hierarchy_succ
  · simpa using pair_mem_hierarchy_succ hx hx
  · exact pair_mem_hierarchy_succ hx hy

theorem common_hierarchy_stage {κ x y : V} [IsOrdinal κ]
    (hκ : ∀ β ∈ κ, succ β ∈ κ) (hx : x ∈ hierarchy κ) (hy : y ∈ hierarchy κ) :
    ∃ β ∈ κ, x ∈ hierarchy β ∧ y ∈ hierarchy β := by
  obtain ⟨β, hβ, hxβ⟩ := (hierarchy_limit κ hκ x).mp hx
  obtain ⟨γ, hγ, hyγ⟩ := (hierarchy_limit κ hκ y).mp hy
  have : IsOrdinal β := IsOrdinal.of_mem hβ
  have : IsOrdinal γ := IsOrdinal.of_mem hγ
  rcases IsOrdinal.subset_or_supset β γ with h | h
  · exact ⟨γ, hγ, hierarchy_mono h x hxβ, hyγ⟩
  · exact ⟨β, hβ, hxβ, hierarchy_mono h y hyγ⟩

theorem mem_hierarchy_of_mem_stage {κ β x : V} [IsOrdinal κ]
    (hβ : β ∈ κ) (hx : x ∈ hierarchy β) : x ∈ hierarchy κ := by
  have : IsOrdinal β := IsOrdinal.of_mem hβ
  exact hierarchy_mono (IsOrdinal.toIsTransitive.transitive β hβ) x hx

theorem power_mem_hierarchy_limit {κ x : V} [IsOrdinal κ]
    (hκ : ∀ β ∈ κ, succ β ∈ κ) (hx : x ∈ hierarchy κ) : ℘ x ∈ hierarchy κ := by
  have hr : rank x ∈ κ := (mem_hierarchy_iff_rank_mem x κ).mp hx
  apply mem_hierarchy_of_mem_stage (hκ _ (hκ _ hr))
  rw [hierarchy_succ, mem_power_iff]
  intro y hy
  rw [hierarchy_succ, mem_power_iff]
  exact subset_trans (mem_power_iff.mp hy) (subset_hierarchy_rank x)

theorem pair_mem_hierarchy_limit {κ x y : V} [IsOrdinal κ]
    (hκ : ∀ β ∈ κ, succ β ∈ κ) (hx : x ∈ hierarchy κ) (hy : y ∈ hierarchy κ) :
    ({x, y} : V) ∈ hierarchy κ := by
  obtain ⟨β, hβ, hxβ, hyβ⟩ := common_hierarchy_stage hκ hx hy
  have : IsOrdinal β := IsOrdinal.of_mem hβ
  exact mem_hierarchy_of_mem_stage (hκ β hβ) (pair_mem_hierarchy_succ hxβ hyβ)

theorem kpair_mem_hierarchy_limit {κ x y : V} [IsOrdinal κ]
    (hκ : ∀ β ∈ κ, succ β ∈ κ) (hx : x ∈ hierarchy κ) (hy : y ∈ hierarchy κ) :
    ⟨x, y⟩ₖ ∈ hierarchy κ := by
  obtain ⟨β, hβ, hxβ, hyβ⟩ := common_hierarchy_stage hκ hx hy
  have : IsOrdinal β := IsOrdinal.of_mem hβ
  exact mem_hierarchy_of_mem_stage (hκ _ (hκ _ hβ))
    (kpair_mem_hierarchy_succ_succ hxβ hyβ)

theorem prod_mem_hierarchy_limit {κ X Y : V} [IsOrdinal κ]
    (hκ : ∀ β ∈ κ, succ β ∈ κ) (hX : X ∈ hierarchy κ) (hY : Y ∈ hierarchy κ) :
    X ×ˢ Y ∈ hierarchy κ := by
  obtain ⟨β, hβ, hXβ, hYβ⟩ := common_hierarchy_stage hκ hX hY
  have : IsOrdinal β := IsOrdinal.of_mem hβ
  apply mem_hierarchy_of_mem_stage (hκ _ (hκ _ (hκ _ hβ)))
  rw [hierarchy_succ, mem_power_iff]
  intro p hp
  obtain ⟨x, hx, y, hy, rfl⟩ := mem_prod_iff.mp hp
  exact kpair_mem_hierarchy_succ_succ
    ((hierarchy_transitive β).mem_trans hx hXβ)
    ((hierarchy_transitive β).mem_trans hy hYβ)

end ZFVP
