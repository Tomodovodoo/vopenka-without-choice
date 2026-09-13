import ZFVP.SetTheory.ForcingBoundThreadSections
import ZFVP.SetTheory.DirectLimitClosure
import ZFVP.SetTheory.FiniteCofinality

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem forcingFamily_eq_section_of_support {θ P π E U I f k : V} [IsOrdinal θ]
    (h : IsSplitForcingSystem θ P π E) (hk : k ∈ θ) (hU : ∀ j ∈ θ, P ‘ j ⊆ U)
    (hf : f ∈ (forcingInverseLimit θ P π U) ^ I)
    (hs : ∀ a ∈ I, IsThreadSupport θ E (f ‘ a) k) :
    f = compose (forcingCoordinateFamily I f k) (forcingThreadSection θ P π E k) := by
  have hb := forcingCoordinateFamily_mem hf hk
  have hm := forcingThreadSection_maps h hk hU
  have hc := compose_function hb hm
  let := IsFunction.of_mem hf
  let := IsFunction.of_mem hc
  apply functions_eq_of_domain_values
  · rw [domain_eq_of_mem_function hf, domain_eq_of_mem_function hc]
  · intro a ha
    rw [domain_eq_of_mem_function hf] at ha
    have hfa := function_value_mem hf ha
    have hka := function_value_mem hb ha
    rw [value_compose_of_mem_function hb hm ha, forcingThreadSection_value hka]
    apply forcingThread_eq_of_support hfa
      (forcingDirectLimit_subset _ _ _ _ _ _ (forcingSectionThread_mem h hk hka hU))
      (hs a ha) (forcingSectionThread_support h hk hka)
    rw [forcingSectionThread_value hk, forcingSectionValue_self h hk hka,
      forcingCoordinateFamily_value ha]

theorem forcingBoundThread_mem_direct {θ P R π E B U i I f p : V} [IsOrdinal θ]
    (h : IsSplitForcingSystem θ P π E) (m : IsFunctionalSplitForcingSystem θ P π E)
    (hB : IsCoherentForcingBound θ P R π B i I)
    (hc : IsSectionCompatibleForcingBound θ P R π E B i I)
    (hi : i ∈ θ) (hI : I ∈ internalCofinality θ) (hU : ∀ j ∈ θ, P ‘ j ⊆ U)
    (hf : IsForcingDirectedFamily (forcingDirectLimit θ P π E U)
      (forcingThreadOrder θ R (forcingDirectLimit θ P π E U)) I f)
    (hp : p ∈ P ‘ i) (hb : ∀ a ∈ I, ⟨p, (f ‘ a) ‘ i⟩ₖ ∈ R ‘ i) :
    forcingBoundThread θ π B I f i p ∈ forcingDirectLimit θ P π E U := by
  have hfi : IsForcingDirectedFamily (forcingInverseLimit θ P π U)
      (forcingThreadOrder θ R (forcingInverseLimit θ P π U)) I f := by
    refine ⟨mem_function_of_mem_function_of_subset hf.1 (forcingDirectLimit_subset _ _ _ _ _), ?_⟩
    intro a ha b hb
    obtain ⟨c, hc, hca, hcb⟩ := hf.2 a ha b hb
    refine ⟨c, hc, ?_, ?_⟩
    · obtain ⟨hc', ha', he⟩ := (mem_forcingThreadOrder_iff _ _ _ _ _).mp hca
      exact (mem_forcingThreadOrder_iff _ _ _ _ _).mpr
        ⟨forcingDirectLimit_subset _ _ _ _ _ _ hc', forcingDirectLimit_subset _ _ _ _ _ _ ha', he⟩
    · obtain ⟨hc', hb', he⟩ := (mem_forcingThreadOrder_iff _ _ _ _ _).mp hcb
      exact (mem_forcingThreadOrder_iff _ _ _ _ _).mpr
        ⟨forcingDirectLimit_subset _ _ _ _ _ _ hc', forcingDirectLimit_subset _ _ _ _ _ _ hb', he⟩
  obtain ⟨k₀, hk₀, hs₀⟩ := forcingDirectLimit_common_support h hI hf.1
  let := IsOrdinal.of_mem hi
  let := IsOrdinal.of_mem hk₀
  let k := i ∪ k₀
  have hk : k ∈ θ := ordinal_union_mem hi hk₀
  have hik : i ⊆ k := fun z hz ↦ mem_union_iff.mpr (Or.inl hz)
  have hk₀k : k₀ ⊆ k := fun z hz ↦ mem_union_iff.mpr (Or.inr hz)
  have hs (a : V) (ha : a ∈ I) : IsThreadSupport θ E (f ‘ a) k :=
    (hs₀ a ha).raise ((mem_forcingInverseLimit_iff _ _ _ _ _).mp (function_value_mem hfi.1 ha)).2.1
      hk hk₀k (fun j hj hkj q hq ↦ h.secComp k₀ hk₀ k hk j hj hk₀k hkj q hq)
  have hg := forcingCoordinateFamily_directed hfi hk
  have hb' : ∀ a ∈ I, ⟨p, (π ‘ ⟨i, k⟩ₖ) ‘ ((forcingCoordinateFamily I f k) ‘ a)⟩ₖ ∈ R ‘ i := by
    intro a ha
    rw [forcingCoordinateFamily_value ha,
      forcingInverseLimit_project_subset h (function_value_mem hfi.1 ha) hi hk hik]
    exact hb a ha
  have he := forcingFamily_eq_section_of_support h hk hU hfi.1 hs
  have heq := forcingBoundThread_section h m hB hc hi hk hik hU hg hp hb'
  rw [← he] at heq
  rw [heq]
  exact forcingSectionThread_mem h hk (hB.bound k hk hik _ hg p hp hb').1 hU

end ZFVP
