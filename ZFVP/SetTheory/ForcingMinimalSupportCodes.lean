import ZFVP.SetTheory.ForcingMinimalSupport
import ZFVP.SetTheory.ForcingStageThreadMap
import ZFVP.SetTheory.ForcingIsomorphism
import ZFVP.SetTheory.ForcingPullbackOrder

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- Canonical bounded codes for supported threads. The first coordinate is the
least stage from which the thread is a section. -/
noncomputable def forcingMinimalSupportCodes (θ P E U : V) : V :=
  {a ∈ θ ×ˢ U ; IsMinimalSectionPoint P E (kpair.π₁ a) (kpair.π₂ a)}

theorem mem_forcingMinimalSupportCodes_iff (θ P E U a : V) :
    a ∈ forcingMinimalSupportCodes θ P E U ↔
      ∃ k ∈ θ, ∃ p ∈ U, a = ⟨k, p⟩ₖ ∧ IsMinimalSectionPoint P E k p := by
  simp only [forcingMinimalSupportCodes, mem_sep_iff, mem_prod_iff]
  constructor
  · rintro ⟨⟨k, hk, p, hp, rfl⟩, hm⟩
    exact ⟨k, hk, p, hp, rfl, by simpa using hm⟩
  · rintro ⟨k, hk, p, hp, rfl, hm⟩
    exact ⟨⟨k, hk, p, hp, rfl⟩, by simpa using hm⟩

noncomputable def forcingMinimalSupportDecode (θ π E a : V) : V :=
  forcingSectionThread θ π E (kpair.π₁ a) (kpair.π₂ a)

instance forcingMinimalSupportDecode_definable (θ π E : V) :
    ℒₛₑₜ-function₁[V] (forcingMinimalSupportDecode θ π E) := by
  exact forcingStageThread_definable θ π E

@[simp] theorem forcingMinimalSupportDecode_pair (θ π E k p : V) :
    forcingMinimalSupportDecode θ π E ⟨k, p⟩ₖ = forcingSectionThread θ π E k p := by
  simp [forcingMinimalSupportDecode]

theorem forcingMinimalSupportDecode_mem {θ P π E U a : V} [IsOrdinal θ]
    (h : IsSplitForcingSystem θ P π E) (hU : ∀ i ∈ θ, P ‘ i ⊆ U)
    (ha : a ∈ forcingMinimalSupportCodes θ P E U) :
    forcingMinimalSupportDecode θ π E a ∈ forcingDirectLimit θ P π E U := by
  obtain ⟨k, hk, p, _, rfl, hp⟩ := (mem_forcingMinimalSupportCodes_iff _ _ _ _ _).mp ha
  simpa only [forcingMinimalSupportDecode_pair] using forcingSectionThread_mem h hk hp.1 hU

theorem forcingMinimalSupportDecode_injective {θ P π E U a b : V} [IsOrdinal θ]
    (h : IsSplitForcingSystem θ P π E) (hU : ∀ i ∈ θ, P ‘ i ⊆ U)
    (ha : a ∈ forcingMinimalSupportCodes θ P E U) (hb : b ∈ forcingMinimalSupportCodes θ P E U)
    (he : forcingMinimalSupportDecode θ π E a = forcingMinimalSupportDecode θ π E b) : a = b := by
  obtain ⟨k, hk, p, _, rfl, hp⟩ := (mem_forcingMinimalSupportCodes_iff _ _ _ _ _).mp ha
  obtain ⟨l, hl, q, _, rfl, hq⟩ := (mem_forcingMinimalSupportCodes_iff _ _ _ _ _).mp hb
  simp only [forcingMinimalSupportDecode_pair] at he
  have hh := minimalSectionPoint_section_injective h hU hk hl hp hq he
  rw [hh.1, hh.2]

theorem forcingMinimalSupportDecode_surjective {θ P π E U f : V} [IsOrdinal θ]
    (h : IsSplitForcingSystem θ P π E) (hU : ∀ i ∈ θ, P ‘ i ⊆ U)
    (hf : f ∈ forcingDirectLimit θ P π E U) :
    ∃ a ∈ forcingMinimalSupportCodes θ P E U, forcingMinimalSupportDecode θ π E a = f := by
  obtain ⟨k, hk, _⟩ := forcingDirectLimit_least_support hf
  have hi := forcingDirectLimit_subset _ _ _ _ _ _ hf
  have hp := minimalSectionPoint_of_least_support h hU hi hk
  refine ⟨⟨k, f ‘ k⟩ₖ, ?_, ?_⟩
  · exact (mem_forcingMinimalSupportCodes_iff _ _ _ _ _).mpr
      ⟨k, hk.2.1.1, f ‘ k, hU k hk.2.1.1 _ hp.1, rfl, hp⟩
  · simpa only [forcingMinimalSupportDecode_pair] using (forcingThread_eq_section_of_support h hi hk.2.1 hU).symm

/-- The pair code of a condition belongs to the endpoint rank whenever all
earlier stage carriers do. Full threads need not belong to that rank. -/
theorem forcingMinimalSupportCodes_subset_hierarchy {θ P E U : V} [IsOrdinal θ]
    (hs : ∀ α ∈ θ, succ α ∈ θ) (hP : ∀ k ∈ θ, P ‘ k ∈ hierarchy θ) :
    forcingMinimalSupportCodes θ P E U ⊆ hierarchy θ := by
  intro a ha
  obtain ⟨k, hk, p, _, rfl, hp⟩ := (mem_forcingMinimalSupportCodes_iff _ _ _ _ _).mp ha
  let := IsOrdinal.of_mem hk
  exact kpair_mem_hierarchy_limit hs (ordinal_subset_hierarchy θ k hk)
    ((hierarchy_transitive θ).mem_trans hp.1 (hP k hk))

noncomputable def forcingMinimalSupportMap (θ P π E U : V) : V :=
  definableGraph (forcingMinimalSupportCodes θ P E U)
    (forcingMinimalSupportDecode θ π E) (forcingMinimalSupportDecode_definable θ π E)

theorem forcingMinimalSupportMap_value {θ P π E U a : V}
    (ha : a ∈ forcingMinimalSupportCodes θ P E U) :
    (forcingMinimalSupportMap θ P π E U) ‘ a = forcingMinimalSupportDecode θ π E a :=
  value_definableGraph _ _ _ ha

/-- The canonical code map is a genuine forcing isomorphism with the pulled-back
order, rather than a surjection with duplicate stage representations. -/
theorem forcingMinimalSupportMap_isomorphism {θ P π E U R : V} [IsOrdinal θ]
    (h : IsSplitForcingSystem θ P π E) (hU : ∀ i ∈ θ, P ‘ i ⊆ U) :
    IsForcingIsomorphism (forcingMinimalSupportCodes θ P E U)
      (forcingPullbackOrder (forcingMinimalSupportCodes θ P E U) R
        (forcingMinimalSupportMap θ P π E U))
      (forcingDirectLimit θ P π E U) R (forcingMinimalSupportMap θ P π E U) := by
  have hm : forcingMinimalSupportMap θ P π E U ∈
      forcingDirectLimit θ P π E U ^ forcingMinimalSupportCodes θ P E U :=
    definableGraph_mem_function_of_mapsTo _ _ _ _ (fun _ ha ↦ forcingMinimalSupportDecode_mem h hU ha)
  refine ⟨hm, ?_, ?_, ?_⟩
  · intro a b f haf hbf
    obtain ⟨ha, hfa⟩ := (pair_mem_definableGraph_iff _ _ _ _ _).mp haf
    obtain ⟨hb, hfb⟩ := (pair_mem_definableGraph_iff _ _ _ _ _).mp hbf
    exact forcingMinimalSupportDecode_injective h hU ha hb (hfa.symm.trans hfb)
  · apply subset_antisymm (range_subset_of_mem_function hm)
    intro f hf
    obtain ⟨a, ha, he⟩ := forcingMinimalSupportDecode_surjective h hU hf
    exact mem_range_of_kpair_mem ((pair_mem_definableGraph_iff _ _ _ a f).mpr ⟨ha, he.symm⟩)
  · intro a ha b hb
    simp only [mem_forcingPullbackOrder_iff, ha, hb, true_and]

end ZFVP
