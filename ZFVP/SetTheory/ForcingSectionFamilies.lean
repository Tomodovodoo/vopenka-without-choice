import ZFVP.SetTheory.ForcingCoordinateFamilies
import ZFVP.SetTheory.ForcingSectionMaps
import ZFVP.SetTheory.ForcingMapExtension

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem forcingSectionValue_below {θ P π E j k p : V} [IsOrdinal θ]
    (h : IsSplitForcingSystem θ P π E) (hj : j ∈ θ) (hk : k ∈ θ) (hkj : k ⊆ j)
    (hp : p ∈ P ‘ j) : forcingSectionValue π E j p k = (π ‘ ⟨k, j⟩ₖ) ‘ p := by
  let := IsOrdinal.of_mem hj
  let := IsOrdinal.of_mem hk
  rcases IsOrdinal.subset_iff.mp hkj with rfl | hkj
  · rw [forcingSectionValue_self h hj hp, h.projId hj hp]
  · simp only [forcingSectionValue, ite_eq_left hkj]

theorem forcingSectionValue_above {π E j k p : V} (hjk : j ⊆ k) :
    forcingSectionValue π E j p k = (E ‘ ⟨j, k⟩ₖ) ‘ p := by
  have hkj : k ∉ j := fun hkj ↦ mem_irrefl k (hjk k hkj)
  simp only [forcingSectionValue, ite_eq_right hkj]

theorem forcingSectionFamily_mem {θ P π E U I f j : V} [IsOrdinal θ]
    (h : IsSplitForcingSystem θ P π E) (hj : j ∈ θ)
    (hU : ∀ k ∈ θ, P ‘ k ⊆ U) (hf : f ∈ (P ‘ j) ^ I) :
    compose f (forcingThreadSection θ P π E j) ∈ (forcingInverseLimit θ P π U) ^ I :=
  mem_function_of_mem_function_of_subset (compose_function hf (forcingThreadSection_maps h hj hU))
    (forcingDirectLimit_subset _ _ _ _ _)

theorem forcingCoordinateFamily_section_below {θ P π E U I f j k : V} [IsOrdinal θ]
    (h : IsSplitForcingSystem θ P π E) (m : IsFunctionalSplitForcingSystem θ P π E)
    (hj : j ∈ θ) (hk : k ∈ θ) (hkj : k ⊆ j) (hU : ∀ a ∈ θ, P ‘ a ⊆ U)
    (hf : f ∈ (P ‘ j) ^ I) :
    forcingCoordinateFamily I (compose f (forcingThreadSection θ P π E j)) k = compose f (π ‘ ⟨k, j⟩ₖ) := by
  have hsec := forcingThreadSection_maps h hj hU
  have hleft := forcingCoordinateFamily_mem (forcingSectionFamily_mem h hj hU hf) hk
  have hm := m.projection k hk j hj hkj
  have hright := compose_function hf hm
  let := IsFunction.of_mem hleft
  let := IsFunction.of_mem hright
  apply functions_eq_of_domain_values
  · rw [domain_eq_of_mem_function hleft, domain_eq_of_mem_function hright]
  · intro a ha
    rw [domain_eq_of_mem_function hleft] at ha
    rw [forcingCoordinateFamily_value ha, value_compose_of_mem_function hf hsec ha,
      forcingThreadSection_value (function_value_mem hf ha), forcingSectionThread_value hk,
      forcingSectionValue_below h hj hk hkj (function_value_mem hf ha), value_compose_of_mem_function hf hm ha]

theorem forcingCoordinateFamily_section_above {θ P π E U I f j k : V} [IsOrdinal θ]
    (h : IsSplitForcingSystem θ P π E) (m : IsFunctionalSplitForcingSystem θ P π E)
    (hj : j ∈ θ) (hk : k ∈ θ) (hjk : j ⊆ k) (hU : ∀ a ∈ θ, P ‘ a ⊆ U)
    (hf : f ∈ (P ‘ j) ^ I) :
    forcingCoordinateFamily I (compose f (forcingThreadSection θ P π E j)) k = compose f (E ‘ ⟨j, k⟩ₖ) := by
  have hsec := forcingThreadSection_maps h hj hU
  have hleft := forcingCoordinateFamily_mem (forcingSectionFamily_mem h hj hU hf) hk
  have hm := m.sectionMap j hj k hk hjk
  have hright := compose_function hf hm
  let := IsFunction.of_mem hleft
  let := IsFunction.of_mem hright
  apply functions_eq_of_domain_values
  · rw [domain_eq_of_mem_function hleft, domain_eq_of_mem_function hright]
  · intro a ha
    rw [domain_eq_of_mem_function hleft] at ha
    rw [forcingCoordinateFamily_value ha, value_compose_of_mem_function hf hsec ha,
      forcingThreadSection_value (function_value_mem hf ha), forcingSectionThread_value hk,
      forcingSectionValue_above hjk, value_compose_of_mem_function hf hm ha]

end ZFVP
