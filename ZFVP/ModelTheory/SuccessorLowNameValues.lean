import ZFVP.ModelTheory.SuccessorLowNameFamily
import ZFVP.ModelTheory.ForcingRealizationGeneration
import ZFVP.SetTheory.EndExtensionRank
import ZFVP.SetTheory.EndExtensionHierarchyAgreement

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V W : Type*} [SetStructure V] [SetStructure W]
  [Nonempty V] [Nonempty W] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [W↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem rankRestrictedName_mem_successorLowNameSet (P R η τ : V) :
    rankRestrictedName P R η τ ∈ successorLowNameSet P η :=
  mem_successorLowNameSet.mpr sep_subset

namespace ForcingRealization
variable {A : ForcingContext V} (L : ForcingRealization A W)

noncomputable def nameValues (N : V) : W :=
  repl (nameValue L.genericSet) (by definability) (L.ground N)

theorem mem_nameValues {N : V} {x : W} :
    x ∈ L.nameValues N ↔ ∃ τ ∈ N, x = nameValue L.genericSet (L.ground τ) := by
  unfold nameValues
  rw [repl_spec (by definability)]
  constructor
  · rintro ⟨t, ht, hx⟩
    obtain ⟨τ, hτ, rfl⟩ := L.ground.endExtension N t ht
    exact ⟨τ, hτ, hx⟩
  · rintro ⟨τ, hτ, hx⟩
    exact ⟨L.ground τ, (L.ground.mem_iff _ _).mpr hτ, hx⟩

theorem mem_nameValue_ground {τ : V} {x : W} :
    x ∈ nameValue L.genericSet (L.ground τ) ↔
      ∃ σ, ∃ p ∈ A.G, ⟨σ, p⟩ₖ ∈ τ ∧ x = nameValue L.genericSet (L.ground σ) := by
  rw [mem_nameValue_iff]
  constructor
  · rintro ⟨s, p, hp, hsp, hx⟩
    obtain ⟨σ, q, hσq, hs, hpq⟩ := (L.ground.pair_mem_image_iff τ s p).mp hsp
    rw [hs] at hx
    rw [hpq] at hp
    exact ⟨σ, q, (L.generic_mem q).mp hp, hσq, hx⟩
  · rintro ⟨σ, p, hp, hσp, hx⟩
    exact ⟨L.ground σ, L.ground p, (L.generic_mem p).mpr hp,
      by rw [← L.ground.map_kpair, L.ground.mem_iff]; exact hσp, hx⟩

theorem low_name_value_mem_hierarchy {η τ : V} [IsOrdinal η]
    (hτ : τ ∈ lowRankNameSet A.P η) :
    nameValue L.genericSet (L.ground τ) ∈ hierarchy (L.ground η) := by
  let := (L.ground.ordinal_iff η).mpr inferInstance
  apply nameValue_mem_hierarchy
  rw [mem_hierarchy_iff_rank_mem, ← L.ground.map_rank, L.ground.mem_iff]
  exact (mem_hierarchy_iff_rank_mem _ _).mp (lowRankNameSet_subset A.P η τ hτ)

theorem low_nameValues_subset_hierarchy (η : V) [IsOrdinal η] :
    L.nameValues (lowRankNameSet A.P η) ⊆ hierarchy (L.ground η) := by
  intro x hx
  obtain ⟨τ, hτ, rfl⟩ := L.mem_nameValues.mp hx
  exact L.low_name_value_mem_hierarchy hτ

theorem successor_low_name_value_subset {η τ : V}
    (hτ : τ ∈ successorLowNameSet A.P η) :
    nameValue L.genericSet (L.ground τ) ⊆ L.nameValues (lowRankNameSet A.P η) := by
  intro x hx
  obtain ⟨σ, p, _, hσp, rfl⟩ := L.mem_nameValue_ground.mp hx
  exact L.mem_nameValues.mpr ⟨σ, successorLowNameSet_subname_low hτ σ
    (mem_domain_of_kpair_mem hσp), rfl⟩

theorem mem_rankRestrictedName_value (η τ : V) (x : W) :
    x ∈ nameValue L.genericSet (L.ground (rankRestrictedName A.P A.R η τ)) ↔
      x ∈ nameValue L.genericSet (L.ground τ) ∧ x ∈ L.nameValues (lowRankNameSet A.P η) := by
  rw [L.mem_nameValue_ground]
  constructor
  · rintro ⟨σ, p, hpG, hp, rfl⟩
    obtain ⟨hσ, _, hpτ⟩ := (pair_mem_rankRestrictedName _ _ _ _ _ _).mp hp
    exact ⟨(L.nameValue_mem_iff σ τ).mpr ⟨p, hpG, hpτ⟩,
      L.mem_nameValues.mpr ⟨σ, hσ, rfl⟩⟩
  · rintro ⟨hx, hy⟩
    obtain ⟨σ, hσ, rfl⟩ := L.mem_nameValues.mp hy
    obtain ⟨p, hpG, hpτ⟩ := (L.nameValue_mem_iff σ τ).mp hx
    exact ⟨σ, p, hpG, (pair_mem_rankRestrictedName _ _ _ _ _ _).mpr
      ⟨hσ, A.generic.1.1 p hpG, hpτ⟩, rfl⟩

theorem rankRestrictedName_value_of_subset {η τ : V}
    (hx : nameValue L.genericSet (L.ground τ) ⊆ L.nameValues (lowRankNameSet A.P η)) :
    nameValue L.genericSet (L.ground (rankRestrictedName A.P A.R η τ)) =
      nameValue L.genericSet (L.ground τ) := by
  apply mem_ext
  intro x
  rw [L.mem_rankRestrictedName_value]
  exact ⟨And.left, fun h ↦ ⟨h, hx x h⟩⟩

theorem mem_successor_low_nameValues_iff (η : V) (x : W) :
    x ∈ L.nameValues (successorLowNameSet A.P η) ↔
      x ⊆ L.nameValues (lowRankNameSet A.P η) ∧
        ∃ τ : ForcingName A.P, x = nameValue L.genericSet (L.ground τ.val) := by
  constructor
  · intro hx
    obtain ⟨τ, hτ, rfl⟩ := L.mem_nameValues.mp hx
    exact ⟨L.successor_low_name_value_subset hτ, ⟨τ, successorLowNameSet_isName hτ⟩, rfl⟩
  · rintro ⟨hx, τ, rfl⟩
    exact L.mem_nameValues.mpr ⟨rankRestrictedName A.P A.R η τ.val,
      rankRestrictedName_mem_successorLowNameSet _ _ _ _, (L.rankRestrictedName_value_of_subset hx).symm⟩

end ForcingRealization
end ZFVP

