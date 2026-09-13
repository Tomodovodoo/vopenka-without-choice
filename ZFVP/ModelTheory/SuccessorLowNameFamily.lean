import ZFVP.ModelTheory.ForcingRankRestrictedNames
import ZFVP.SetTheory.NameValueRank

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def successorLowNameSet (P η : V) : V := power (lowRankNameSet P η ×ˢ P)

theorem mem_successorLowNameSet {P η τ : V} :
    τ ∈ successorLowNameSet P η ↔ τ ⊆ lowRankNameSet P η ×ˢ P := mem_power_iff

instance successorLowNameSet_definable : ℒₛₑₜ-function₂[V] successorLowNameSet := by
  unfold successorLowNameSet
  definability

theorem lowRankNameSet_subnameClosed (P η : V) [IsOrdinal η] :
    IsSubnameClosed (lowRankNameSet P η) := namesBelow_closed P η

theorem lowRankNameSet_member_subset_product {P η τ : V} [IsOrdinal η]
    (hτ : τ ∈ lowRankNameSet P η) : τ ⊆ lowRankNameSet P η ×ˢ P := by
  intro z hz
  obtain ⟨σ, p, hp, rfl, _⟩ := (forcingName_iff _ _).mp
    ((mem_lowRankNameSet _ _ _).mp hτ).2 z hz
  exact kpair_mem_iff.mpr ⟨lowRankNameSet_subnameClosed P η τ hτ σ
    (mem_domain_of_kpair_mem hz), hp⟩

theorem lowRankNameSet_subset_successor (P η : V) [IsOrdinal η] :
    lowRankNameSet P η ⊆ successorLowNameSet P η :=
  fun _ hτ ↦ mem_successorLowNameSet.mpr (lowRankNameSet_member_subset_product hτ)

theorem successorLowNameSet_subname_low {P η τ : V}
    (hτ : τ ∈ successorLowNameSet P η) : domain τ ⊆ lowRankNameSet P η := by
  intro σ hσ
  obtain ⟨p, hp⟩ := mem_domain_iff.mp hσ
  exact (kpair_mem_iff.mp (mem_successorLowNameSet.mp hτ _ hp)).1

theorem successorLowNameSet_subnameClosed (P η : V) [IsOrdinal η] :
    IsSubnameClosed (successorLowNameSet P η) :=
  fun _ hτ σ hσ ↦ lowRankNameSet_subset_successor P η σ
    (successorLowNameSet_subname_low hτ σ hσ)

theorem successorLowNameSet_isName {P η τ : V} (hτ : τ ∈ successorLowNameSet P η) :
    IsForcingName P τ := by
  apply (forcingName_iff _ _).mpr
  intro z hz
  obtain ⟨σ, hσ, p, hp, rfl⟩ := mem_prod_iff.mp (mem_successorLowNameSet.mp hτ z hz)
  exact ⟨σ, p, hp, rfl, ((mem_lowRankNameSet _ _ _).mp hσ).2⟩

theorem lowRankNameSet_product_subset_hierarchy {P η : V} [IsOrdinal η]
    (hη : ∀ β ∈ η, succ β ∈ η) (hP : P ⊆ hierarchy η) :
    lowRankNameSet P η ×ˢ P ⊆ hierarchy η := by
  intro z hz
  obtain ⟨σ, hσ, p, hp, rfl⟩ := mem_prod_iff.mp hz
  exact kpair_mem_hierarchy_limit hη (lowRankNameSet_subset P η σ hσ) (hP p hp)

theorem successorLowNameSet_member_subset_hierarchy {P η τ : V} [IsOrdinal η]
    (hη : ∀ β ∈ η, succ β ∈ η) (hP : P ⊆ hierarchy η)
    (hτ : τ ∈ successorLowNameSet P η) : τ ⊆ hierarchy η :=
  fun z hz ↦ lowRankNameSet_product_subset_hierarchy hη hP z (mem_successorLowNameSet.mp hτ z hz)

theorem successorLowNameSet_member_rank {P η τ : V} [IsOrdinal η]
    (hη : ∀ β ∈ η, succ β ∈ η) (hP : P ⊆ hierarchy η)
    (hτ : τ ∈ successorLowNameSet P η) : rank τ ⊆ η :=
  rank_minimal _ _ inferInstance (successorLowNameSet_member_subset_hierarchy hη hP hτ)

theorem successorLowNameSet_subset_hierarchy {P η : V} [IsOrdinal η]
    (hη : ∀ β ∈ η, succ β ∈ η) (hP : P ⊆ hierarchy η) :
    successorLowNameSet P η ⊆ hierarchy (succ η) := by
  intro τ hτ
  rw [hierarchy_succ, mem_power_iff]
  exact successorLowNameSet_member_subset_hierarchy hη hP hτ

theorem successorLowNameSet_rank {P η : V} [IsOrdinal η]
    (hη : ∀ β ∈ η, succ β ∈ η) (hP : P ⊆ hierarchy η) :
    rank (successorLowNameSet P η) ⊆ succ η :=
  rank_minimal _ _ inferInstance (successorLowNameSet_subset_hierarchy hη hP)

theorem successorLowNameSet_mem_second_successor {P η : V} [IsOrdinal η]
    (hη : ∀ β ∈ η, succ β ∈ η) (hP : P ⊆ hierarchy η) :
    successorLowNameSet P η ∈ hierarchy (succ (succ η)) := by
  rw [hierarchy_succ, mem_power_iff]
  exact successorLowNameSet_subset_hierarchy hη hP

theorem successorLowNameSet_mem_finite_rank {P η : V} [IsOrdinal η]
    (hη : ∀ β ∈ η, succ β ∈ η) (hP : P ⊆ hierarchy η) :
    successorLowNameSet P η ∈ hierarchy (ordinalAdd η (ω : V)) :=
  mem_hierarchy_of_mem_stage
    (ordinalAdd_omega_succ_closed η (ordinalAdd_omega_succ_closed η (ordinalAdd_omega_gt η)))
    (successorLowNameSet_mem_second_successor hη hP)

end ZFVP

