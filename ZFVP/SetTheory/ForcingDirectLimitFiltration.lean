import ZFVP.SetTheory.ForcingSectionMaps

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem forcingThread_eq_section_of_support {θ P π E U f k : V} [IsOrdinal θ]
    (h : IsSplitForcingSystem θ P π E) (hf : f ∈ forcingInverseLimit θ P π U)
    (hk : IsThreadSupport θ E f k) (hU : ∀ i ∈ θ, P ‘ i ⊆ U) :
    f = forcingSectionThread θ π E k (f ‘ k) := by
  have hp := ((mem_forcingInverseLimit_iff _ _ _ _ _).mp hf).2.1 k hk.1
  apply forcingThread_eq_of_support hf
    (forcingDirectLimit_subset _ _ _ _ _ _ (forcingSectionThread_mem h hk.1 hp hU))
    hk (forcingSectionThread_support h hk.1 hp)
  rw [forcingSectionThread_value hk.1, forcingSectionValue_self h hk.1 hp]

/-- Every direct-limit condition is in the range of one canonical section. -/
theorem mem_forcingDirectLimit_iff_section_range {θ P π E U f : V} [IsOrdinal θ]
    (h : IsSplitForcingSystem θ P π E) (hU : ∀ i ∈ θ, P ‘ i ⊆ U) :
    f ∈ forcingDirectLimit θ P π E U ↔
      ∃ k ∈ θ, f ∈ range (forcingThreadSection θ P π E k) := by
  constructor
  · intro hf
    obtain ⟨hf, k, hk⟩ := (mem_forcingDirectLimit_iff _ _ _ _ _ _).mp hf
    have hp := ((mem_forcingInverseLimit_iff _ _ _ _ _).mp hf).2.1 k hk.1
    refine ⟨k, hk.1, ?_⟩
    apply mem_range_of_kpair_mem
    rw [forcingThreadSection, mem_definableGraph_iff]
    exact ⟨f ‘ k, hp, congrArg (fun x : V ↦ ⟨f ‘ k, x⟩ₖ)
      (forcingThread_eq_section_of_support h hf hk hU)⟩
  · rintro ⟨k, hk, hf⟩
    exact range_subset_of_mem_function (forcingThreadSection_maps h hk hU) _ hf

/-- Section ranges form an increasing family inside the direct limit. -/
theorem forcingThreadSection_range_mono {θ P π E U k l : V} [IsOrdinal θ]
    (h : IsSplitForcingSystem θ P π E) (hk : k ∈ θ) (hl : l ∈ θ)
    (hkl : k ⊆ l) (hU : ∀ i ∈ θ, P ‘ i ⊆ U) :
    range (forcingThreadSection θ P π E k) ⊆ range (forcingThreadSection θ P π E l) := by
  intro f hf
  obtain ⟨p, hp⟩ := mem_range_iff.mp hf
  rw [forcingThreadSection, mem_definableGraph_iff] at hp
  obtain ⟨q, hq, he⟩ := hp
  have hval : f = forcingSectionThread θ π E k q := by
    simpa only [kpair.π₂_kpair] using congrArg kpair.π₂ he
  have hq' := h.secMaps k hk l hl hkl q hq
  apply mem_range_of_kpair_mem (x := (E ‘ ⟨k, l⟩ₖ) ‘ q)
  rw [forcingThreadSection, mem_definableGraph_iff]
  refine ⟨(E ‘ ⟨k, l⟩ₖ) ‘ q, hq', ?_⟩
  rw [hval, forcingSectionThread_comp h hk hl hkl hq hU]

end ZFVP
