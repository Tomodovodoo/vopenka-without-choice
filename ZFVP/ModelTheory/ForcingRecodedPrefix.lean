import ZFVP.ModelTheory.ForcingRecodedSystem
import ZFVP.SetTheory.ForcingCodeExtensionValues

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable {θ η s z Q T m Q' T' m' : V}

theorem forcingRecoded_extends
    (hs : IsForcingIterationCode θ s) (hz : IsForcingIterationCode η z)
    (he : ForcingCodeExtends s z) (hθη : θ ⊆ η)
    (hQ : ∀ i ∈ θ, Q ‘ i = Q' ‘ i) (hT : ∀ i ∈ θ, T ‘ i = T' ‘ i)
    (hm : ∀ i ∈ θ, m ‘ i = m' ‘ i)
    (hc : IsForcingIterationCode θ (forcingRecodedCode θ s Q T m))
    (hc' : IsForcingIterationCode η (forcingRecodedCode η z Q' T' m')) :
    ForcingCodeExtends (forcingRecodedCode θ s Q T m) (forcingRecodedCode η z Q' T' m') := by
  apply ForcingCodeExtends.of_values hc hc' hθη
  · simpa only [forcingRecodedCode, forcingCodeP_code] using hQ
  · simpa only [forcingRecodedCode, forcingCodeR_code] using hT
  · intro i hi j hj
    have hv := hs.tableπ.value_of_subset hz.tableπ he.subπ (kpair_mem_iff.mpr ⟨hi, hj⟩)
    simp only [forcingRecodedCode, forcingCodeπ_code]
    rw [forcingRecodedProjections_value hi hj, forcingRecodedProjections_value (hθη i hi) (hθη j hj),
      hm i hi, hm j hj, hv]
  · intro i hi j hj
    have hv := hs.tableE.value_of_subset hz.tableE he.subE (kpair_mem_iff.mpr ⟨hi, hj⟩)
    simp only [forcingRecodedCode, forcingCodeE_code]
    rw [forcingRecodedSections_value hi hj, forcingRecodedSections_value (hθη i hi) (hθη j hj),
      hm i hi, hm j hj, hv]
  · intro i hi j hj
    have hv := hs.tableL.value_of_subset hz.tableL he.subL (kpair_mem_iff.mpr ⟨hi, hj⟩)
    simp only [forcingRecodedCode, forcingCodeL_code, forcingRecodedLifts,
      value_definableGraph _ _ _ (kpair_mem_iff.mpr ⟨hi, hj⟩),
      value_definableGraph _ _ _ (kpair_mem_iff.mpr ⟨hθη i hi, hθη j hj⟩),
      forcingRecodedLiftMap, kpair.π₁_kpair, kpair.π₂_kpair, hQ i hi, hQ j hj, hm i hi, hm j hj, hv]
  · intro i hi
    have hv := hs.tablet.value_of_subset hz.tablet he.subt hi
    simp only [forcingRecodedCode, forcingCodet_code]
    rw [forcingRecodedTops_value hi, forcingRecodedTops_value (hθη i hi), hm i hi, hv]

end ZFVP
