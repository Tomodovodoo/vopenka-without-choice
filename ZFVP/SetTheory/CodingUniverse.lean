import ZFVP.SetTheory.RankBounds
import ZFVP.SetTheory.FiniteSequences

/-! An internal transitive set large enough for finite coding over a given set. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem subset_mem_hierarchy_limit {κ x y : V} [IsOrdinal κ]
    (hκ : ∀ β ∈ κ, succ β ∈ κ) (hy : y ∈ hierarchy κ) (hxy : x ⊆ y) :
    x ∈ hierarchy κ :=
  (hierarchy_transitive κ).mem_trans (mem_power_iff.mpr hxy) (power_mem_hierarchy_limit hκ hy)

theorem function_mem_hierarchy_limit {κ X Y : V} [IsOrdinal κ]
    (hκ : ∀ β ∈ κ, succ β ∈ κ) (hX : X ∈ hierarchy κ) (hY : Y ∈ hierarchy κ) :
    Y ^ X ∈ hierarchy κ := by
  apply subset_mem_hierarchy_limit hκ
    (power_mem_hierarchy_limit hκ (prod_mem_hierarchy_limit hκ hX hY))
  intro f hf
  exact mem_power_iff.mpr (subset_prod_of_mem_function hf)

theorem finiteSequences_mem_hierarchy_limit {κ A : V} [IsOrdinal κ]
    (hκ : ∀ β ∈ κ, succ β ∈ κ) (hω : (ω : V) ∈ hierarchy κ) (hA : A ∈ hierarchy κ) :
    finiteSequences A ∈ hierarchy κ := by
  apply subset_mem_hierarchy_limit hκ
    (power_mem_hierarchy_limit hκ (prod_mem_hierarchy_limit hκ hω hA))
  intro s hs
  exact (show s ∈ ℘ ((ω : V) ×ˢ A) ∧ ∃ n ∈ (ω : V), s ∈ A ^ n from by
    simpa [finiteSequences] using hs).1

noncomputable def codingRank (X : V) : V := ordinalAdd (rank (X ∪ {(ω : V)})) ω

instance codingRank_ordinal (X : V) : IsOrdinal (codingRank X) :=
  ordinalAdd_ordinal _ _

theorem codingRank_succ_closed (X : V) {β : V} (hβ : β ∈ codingRank X) :
    succ β ∈ codingRank X := ordinalAdd_omega_succ_closed _ hβ

noncomputable def codingUniverse (X : V) : V := hierarchy (codingRank X)

instance codingUniverse_transitive (X : V) : IsTransitive (codingUniverse X) :=
  hierarchy_transitive _

theorem self_mem_codingUniverse (X : V) : X ∈ codingUniverse X := by
  change X ∈ hierarchy (codingRank X)
  rw [mem_hierarchy_iff_rank_mem]
  have hgt : rank (X ∪ {(ω : V)}) ∈ codingRank X := ordinalAdd_omega_gt _
  have hs : rank X ⊆ rank (X ∪ {(ω : V)}) := rank_mono (by
    intro x hx
    simp [hx])
  rcases IsOrdinal.subset_iff.mp hs with heq | hlt
  · exact heq ▸ hgt
  · exact IsOrdinal.toIsTransitive.mem_trans hlt hgt

theorem omega_mem_codingUniverse (X : V) : (ω : V) ∈ codingUniverse X := by
  change (ω : V) ∈ hierarchy (codingRank X)
  rw [mem_hierarchy_iff_rank_mem, rank_of_ordinal]
  have hω : rank (ω : V) ∈ rank (X ∪ {(ω : V)}) := rank_mem (by simp)
  rw [rank_of_ordinal (ω : V)] at hω
  exact IsOrdinal.toIsTransitive.mem_trans hω (ordinalAdd_omega_gt _)

theorem codingUniverse_pair_closed {X x y : V}
    (hx : x ∈ codingUniverse X) (hy : y ∈ codingUniverse X) :
    ({x, y} : V) ∈ codingUniverse X :=
  pair_mem_hierarchy_limit (fun _ ↦ codingRank_succ_closed X) hx hy

theorem codingUniverse_kpair_closed {X x y : V}
    (hx : x ∈ codingUniverse X) (hy : y ∈ codingUniverse X) :
    ⟨x, y⟩ₖ ∈ codingUniverse X :=
  kpair_mem_hierarchy_limit (fun _ ↦ codingRank_succ_closed X) hx hy

theorem codingUniverse_power_closed {X x : V} (hx : x ∈ codingUniverse X) :
    ℘ x ∈ codingUniverse X := power_mem_hierarchy_limit (fun _ ↦ codingRank_succ_closed X) hx

theorem codingUniverse_finiteSequences_closed {X A : V} (hA : A ∈ codingUniverse X) :
    finiteSequences A ∈ codingUniverse X :=
  finiteSequences_mem_hierarchy_limit (fun _ ↦ codingRank_succ_closed X)
    (omega_mem_codingUniverse X) hA

end ZFVP
