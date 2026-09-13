import ZFVP.SetTheory.ForcingDirectLimitFiltration
import ZFVP.SetTheory.RankBounds

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- A direct-limit condition represented by its support stage and its value there. -/
noncomputable def forcingStageConditions (θ P U : V) : V :=
  {z ∈ θ ×ˢ U ; kpair.π₂ z ∈ P ‘ (kpair.π₁ z)}

theorem kpair_mem_forcingStageConditions_iff (θ P U k p : V) :
    ⟨k, p⟩ₖ ∈ forcingStageConditions θ P U ↔ k ∈ θ ∧ p ∈ U ∧ p ∈ P ‘ k := by
  simp only [forcingStageConditions, mem_sep_iff, kpair_mem_iff,
    kpair.π₁_kpair, kpair.π₂_kpair]
  tauto

theorem mem_forcingStageConditions_iff (θ P U z : V) :
    z ∈ forcingStageConditions θ P U ↔
      ∃ k ∈ θ, ∃ p ∈ U, p ∈ P ‘ k ∧ z = ⟨k, p⟩ₖ := by
  constructor
  · intro hz
    have hz' := (mem_sep_iff.mp hz).1
    obtain ⟨k, hk, p, hp, rfl⟩ := mem_prod_iff.mp hz'
    exact ⟨k, hk, p, hp, ((kpair_mem_forcingStageConditions_iff _ _ _ _ _).mp hz).2.2, rfl⟩
  · rintro ⟨k, hk, p, hp, hpk, rfl⟩
    exact (kpair_mem_forcingStageConditions_iff _ _ _ _ _).mpr ⟨hk, hp, hpk⟩

/-- Stage codes have small rank even when their corresponding threads do not. -/
theorem forcingStageConditions_subset_hierarchy {θ P U : V} [IsOrdinal θ]
    (hθ : ∀ β ∈ θ, succ β ∈ θ) (hP : ∀ k ∈ θ, P ‘ k ⊆ hierarchy θ) :
    forcingStageConditions θ P U ⊆ hierarchy θ := by
  intro z hz
  obtain ⟨k, hk, p, _, hp, rfl⟩ := (mem_forcingStageConditions_iff _ _ _ _).mp hz
  exact kpair_mem_hierarchy_limit hθ (ordinal_subset_hierarchy θ k hk) (hP k hk p hp)

/-- Every thread in the direct limit has a stage-code representative. -/
theorem mem_forcingDirectLimit_iff_stage_condition {θ P π E U f : V} [IsOrdinal θ]
    (h : IsSplitForcingSystem θ P π E) (hU : ∀ i ∈ θ, P ‘ i ⊆ U) :
    f ∈ forcingDirectLimit θ P π E U ↔ ∃ z ∈ forcingStageConditions θ P U,
      f = forcingSectionThread θ π E (kpair.π₁ z) (kpair.π₂ z) := by
  constructor
  · intro hf
    obtain ⟨hf, k, hk⟩ := (mem_forcingDirectLimit_iff _ _ _ _ _ _).mp hf
    have hp := ((mem_forcingInverseLimit_iff _ _ _ _ _).mp hf).2.1 k hk.1
    refine ⟨⟨k, f ‘ k⟩ₖ, (kpair_mem_forcingStageConditions_iff _ _ _ _ _).mpr
      ⟨hk.1, hU k hk.1 _ hp, hp⟩, ?_⟩
    simpa only [kpair.π₁_kpair, kpair.π₂_kpair] using
      forcingThread_eq_section_of_support h hf hk hU
  · rintro ⟨z, hz, rfl⟩
    obtain ⟨k, hk, p, _, hp, rfl⟩ := (mem_forcingStageConditions_iff _ _ _ _).mp hz
    simpa only [kpair.π₁_kpair, kpair.π₂_kpair] using forcingSectionThread_mem h hk hp hU

end ZFVP
