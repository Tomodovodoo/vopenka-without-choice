import ZFVP.ModelTheory.WoodinNormalizationRecursion
import ZFVP.ModelTheory.WoodinCoordinateProjection

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem woodinNormalizationHistory_prefix_family {Ω θ : V} [IsOrdinal θ]
    (hs : ∀ j ∈ θ, IsWoodinIteration Ω (succ j) (kpair.π₁ (woodinIterationRec j))
      (kpair.π₂ (woodinIterationRec j)))
    (h : ∀ j ∈ θ, IsForcingNormalizationFamily (succ j) (kpair.π₁ (woodinIterationRec j))
      (woodinNormalizationHistory (succ j))) :
    IsForcingNormalizationFamily θ (woodinIterationPrefix θ) (woodinNormalizationHistory θ) := by
  refine ⟨woodinNormalizationHistory_table _, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    rw [woodinIterationPrefix_poset_value hs hi (mem_succ_self i),
      woodinIterationPrefix_order_value hs hi (mem_succ_self i), woodinNormalizationHistory_value hi]
    simpa only [woodinNormalizationHistory_value (mem_succ_self i)] using
      (h i hi).retraction i (mem_succ_self i)
  · intro i hi p hp
    rw [woodinIterationPrefix_poset_value hs hi (mem_succ_self i)] at hp
    rw [woodinIterationPrefix_order_value hs hi (mem_succ_self i), woodinNormalizationHistory_value hi]
    simpa only [woodinNormalizationHistory_value (mem_succ_self i)] using
      (h i hi).equivalent i (mem_succ_self i) p hp
  · intro i hi
    rw [woodinIterationPrefix_top_value hs hi (mem_succ_self i), woodinNormalizationHistory_value hi]
    simpa only [woodinNormalizationHistory_value (mem_succ_self i)] using
      (h i hi).fixesTop i (mem_succ_self i)
  · intro j hj i hij hi p hp
    have hij' : i ∈ succ j := mem_succ_iff.mpr (Or.inr hij)
    rw [woodinIterationPrefix_poset_value hs hj (mem_succ_self j)] at hp
    rw [woodinIterationPrefix_projection_value hs hj hij' (mem_succ_self j),
      woodinNormalizationHistory_value hj, woodinNormalizationHistory_value hi]
    simpa only [woodinNormalizationHistory_value (mem_succ_self j), woodinNormalizationHistory_value hij'] using
      (h j hj).projection j (mem_succ_self j) i hij hij' p hp
  · intro i hi j hj hij p hp
    let := IsOrdinal.of_mem hi
    let := IsOrdinal.of_mem hj
    have hij' : i ∈ succ j := mem_succ_iff.mpr (IsOrdinal.subset_iff.mp hij)
    rw [woodinIterationPrefix_poset_value hs hj hij'] at hp
    rw [woodinIterationPrefix_section_value hs hj hij' (mem_succ_self j),
      woodinNormalizationHistory_value hj, woodinNormalizationHistory_value hi]
    simpa only [woodinNormalizationHistory_value (mem_succ_self j), woodinNormalizationHistory_value hij'] using
      (h j hj).sectionCoherent i hij' j (mem_succ_self j) hij p hp

end ZFVP
