import ZFVP.ModelTheory.SuccessorBoundOperations
import ZFVP.SetTheory.ForcingBoundSectionCompatibility

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem twoStepUnionBound_empty_tails {I p f : V} (h : ∀ a ∈ I, kpair.π₂ (f ‘ a) = ∅) :
    twoStepUnionBound I p f = ⟨p, ∅⟩ₖ := by
  have he : ⋃ˢ range (twoStepTailSequence I f) = ∅ := by
    apply subset_empty_iff_eq_empty.mp
    intro z hz
    obtain ⟨y, hy, hzy⟩ := mem_sUnion_iff.mp hz
    obtain ⟨a, ha⟩ := mem_range_iff.mp hy
    change ⟨a, y⟩ₖ ∈ definableGraph I (fun b ↦ kpair.π₂ (f ‘ b)) (by definability) at ha
    obtain ⟨haI, rfl⟩ := (pair_mem_definableGraph_iff _ _ _ _ _).mp ha
    rw [h a haI] at hzy
    exact hzy
  simp only [twoStepUnionBound, he]

theorem successor_sectionCompatibleBoundColumn {θ P R π E B i k Q S one I : V}
    (h : IsSplitForcingSystem θ P π E) (m : IsFunctionalSplitForcingSystem θ P π E)
    (hB : IsCoherentForcingBound θ P R π B i I)
    (hc : IsSectionCompatibleForcingBound θ P R π E B i I) (hk : k ∈ θ)
    (hmax : ∀ j ∈ θ, j ⊆ k)
    (hR : IsForcingPreorder (P ‘ k) (R ‘ k)) (htop : IsForcingTop (P ‘ k) (R ‘ k) one)
    (hQ : IsForcingIterand (P ‘ k) (R ‘ k) Q S ∅) :
    IsSectionCompatibleBoundColumn θ P R π B (successorSectionColumn θ P E k ∅)
      (forcingSuccessorBound (twoStepConditions (P ‘ k) (R ‘ k) Q ∅) (P ‘ i)
        (twoStepProjection (P ‘ k) (R ‘ k) Q ∅) (B ‘ k) I) i I := by
  constructor
  intro j hj hij f hf p hp hb
  have hm := (successor_functionalColumn h hk hmax hR htop hQ).sectionMap j hj
  have hg := compose_function hf.1 hm
  have hv := (twoStep_projection hR htop hQ).maps
  have hE := m.sectionMap j hj k hk (hmax j hj)
  have he : compose (compose f ((successorSectionColumn θ P E k ∅) ‘ j))
      (twoStepProjection (P ‘ k) (R ‘ k) Q ∅) = compose f (E ‘ ⟨j, k⟩ₖ) := by
    have hl := compose_function hg hv
    have hr := compose_function hf.1 hE
    let := IsFunction.of_mem hl
    let := IsFunction.of_mem hr
    apply functions_eq_of_domain_values
    · rw [domain_eq_of_mem_function hl, domain_eq_of_mem_function hr]
    · intro a ha
      rw [domain_eq_of_mem_function hl] at ha
      rw [value_compose_of_mem_function hg hv ha, twoStepProjection_value (function_value_mem hg ha),
        value_compose_of_mem_function hf.1 hm ha, successorSectionColumn_value hj (function_value_mem hf.1 ha),
        kpair.π₁_kpair, value_compose_of_mem_function hf.1 hE ha]
  rw [forcingSuccessorBound_value hg hp, twoStepUnionBound_empty_tails (fun a ha ↦ by
    rw [value_compose_of_mem_function hf.1 hm ha, successorSectionColumn_value hj (function_value_mem hf.1 ha),
      kpair.π₂_kpair]), he, hc.compatible j hj k hk hij (hmax j hj) f hf p hp hb,
    successorSectionColumn_value hj (hB.bound j hj hij f hf p hp hb).1]

end ZFVP
