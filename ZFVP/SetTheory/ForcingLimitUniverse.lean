import ZFVP.SetTheory.ForcingDirectLimit

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem forcingInverseLimit_change_universe {θ P π U W f : V}
    (hf : f ∈ forcingInverseLimit θ P π U) (hW : ∀ i ∈ θ, P ‘ i ⊆ W) :
    f ∈ forcingInverseLimit θ P π W := by
  obtain ⟨hfun, hm, hc⟩ := (mem_forcingInverseLimit_iff _ _ _ _ _).mp hf
  let := IsFunction.of_mem hfun
  refine (mem_forcingInverseLimit_iff _ _ _ _ _).mpr ⟨?_, hm, hc⟩
  apply mem_function_of_mem_function_of_subset (mem_function_range_of_mem_function hfun)
  intro y hy
  obtain ⟨i, hiy⟩ := mem_range_iff.mp hy
  have hi : i ∈ θ := domain_eq_of_mem_function hfun ▸ mem_domain_of_kpair_mem hiy
  exact value_eq_of_kpair_mem hiy ▸ hW i hi (f ‘ i) (hm i hi)

theorem forcingInverseLimit_universe_eq {θ P π U W : V}
    (hU : ∀ i ∈ θ, P ‘ i ⊆ U) (hW : ∀ i ∈ θ, P ‘ i ⊆ W) :
    forcingInverseLimit θ P π U = forcingInverseLimit θ P π W := by
  apply mem_ext
  intro f
  exact ⟨fun hf ↦ forcingInverseLimit_change_universe hf hW,
    fun hf ↦ forcingInverseLimit_change_universe hf hU⟩

theorem forcingDirectLimit_change_universe {θ P π E U W f : V}
    (hf : f ∈ forcingDirectLimit θ P π E U) (hW : ∀ i ∈ θ, P ‘ i ⊆ W) :
    f ∈ forcingDirectLimit θ P π E W := by
  obtain ⟨hi, hs⟩ := (mem_forcingDirectLimit_iff _ _ _ _ _ _).mp hf
  exact (mem_forcingDirectLimit_iff _ _ _ _ _ _).mpr ⟨forcingInverseLimit_change_universe hi hW, hs⟩

theorem forcingDirectLimit_universe_eq {θ P π E U W : V}
    (hU : ∀ i ∈ θ, P ‘ i ⊆ U) (hW : ∀ i ∈ θ, P ‘ i ⊆ W) :
    forcingDirectLimit θ P π E U = forcingDirectLimit θ P π E W := by
  apply mem_ext
  intro f
  exact ⟨fun hf ↦ forcingDirectLimit_change_universe hf hW,
    fun hf ↦ forcingDirectLimit_change_universe hf hU⟩

end ZFVP
