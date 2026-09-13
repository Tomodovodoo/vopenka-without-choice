import ZFVP.SetTheory.ForcingDirectedMaps
import ZFVP.SetTheory.ForcingThreadMaps
import ZFVP.SetTheory.ForcingSectionThread
import ZFVP.SetTheory.FunctionUnion

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def forcingCoordinateFamily (I f k : V) : V :=
  definableGraph I (fun a ↦ (f ‘ a) ‘ k) (by definability)

instance forcingCoordinateFamily_definable : ℒₛₑₜ-function₃[V] forcingCoordinateFamily := by
  have h : ℒₛₑₜ-relation₄ (fun b I f k : V ↦ ∀ z, z ∈ b ↔ ∃ a ∈ I, z = ⟨a, (f ‘ a) ‘ k⟩ₖ) := by definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = forcingCoordinateFamily (v 1) (v 2) (v 3) ↔ _
  rw [mem_ext_iff]
  simp only [forcingCoordinateFamily, mem_definableGraph_iff]

theorem forcingCoordinateFamily_value {I f k a : V} (ha : a ∈ I) :
    (forcingCoordinateFamily I f k) ‘ a = (f ‘ a) ‘ k := value_definableGraph _ _ _ ha

theorem forcingCoordinateFamily_mem {θ P π U I f k : V}
    (hf : f ∈ (forcingInverseLimit θ P π U) ^ I) (hk : k ∈ θ) :
    forcingCoordinateFamily I f k ∈ (P ‘ k) ^ I := by
  apply definableGraph_mem_function_of_mapsTo
  intro a ha
  exact ((mem_forcingInverseLimit_iff _ _ _ _ _).mp (function_value_mem hf ha)).2.1 k hk

theorem forcingCoordinateFamily_directed {θ P R π U I f k : V}
    (hf : IsForcingDirectedFamily (forcingInverseLimit θ P π U)
      (forcingThreadOrder θ R (forcingInverseLimit θ P π U)) I f) (hk : k ∈ θ) :
    IsForcingDirectedFamily (P ‘ k) (R ‘ k) I (forcingCoordinateFamily I f k) := by
  refine ⟨forcingCoordinateFamily_mem hf.1 hk, ?_⟩
  intro a ha b hb
  obtain ⟨c, hc, hca, hcb⟩ := hf.2 a ha b hb
  refine ⟨c, hc, ?_, ?_⟩
  · rw [forcingCoordinateFamily_value hc, forcingCoordinateFamily_value ha]
    exact ((mem_forcingThreadOrder_iff _ _ _ _ _).mp hca).2.2 k hk
  · rw [forcingCoordinateFamily_value hc, forcingCoordinateFamily_value hb]
    exact ((mem_forcingThreadOrder_iff _ _ _ _ _).mp hcb).2.2 k hk

theorem forcingCoordinateFamily_project {θ P π E U I f j k : V} [IsOrdinal θ]
    (h : IsSplitForcingSystem θ P π E)
    (hf : f ∈ (forcingInverseLimit θ P π U) ^ I) (hj : j ∈ θ) (hk : k ∈ θ) (hjk : j ⊆ k)
    (hm : (π ‘ ⟨j, k⟩ₖ) ∈ (P ‘ j) ^ (P ‘ k)) :
    compose (forcingCoordinateFamily I f k) (π ‘ ⟨j, k⟩ₖ) = forcingCoordinateFamily I f j := by
  have hkf := forcingCoordinateFamily_mem hf hk
  have hjf := forcingCoordinateFamily_mem hf hj
  have hc := compose_function hkf hm
  let := IsFunction.of_mem hc
  let := IsFunction.of_mem hjf
  apply functions_eq_of_domain_values
  · rw [domain_eq_of_mem_function hc, domain_eq_of_mem_function hjf]
  · intro a ha
    rw [domain_eq_of_mem_function hc] at ha
    rw [value_compose_of_mem_function hkf hm ha, forcingCoordinateFamily_value ha,
      forcingCoordinateFamily_value ha]
    exact forcingInverseLimit_project_subset h (function_value_mem hf ha) hj hk hjk

end ZFVP
