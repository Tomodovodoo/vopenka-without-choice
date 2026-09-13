import ZFVP.ModelTheory.ForcingNormalizedCode
import ZFVP.SetTheory.ForcingCodeExtensionValues

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable {θ η s z m n : V}

theorem forcingNormalized_extends
    (hs : IsForcingIterationCode θ s) (hz : IsForcingIterationCode η z)
    (he : ForcingCodeExtends s z) (hθη : θ ⊆ η)
    (hm : ∀ i ∈ θ, m ‘ i = n ‘ i)
    (hc : IsForcingIterationCode θ (forcingNormalizedCode θ s m))
    (hd : IsForcingIterationCode η (forcingNormalizedCode η z n)) :
    ForcingCodeExtends (forcingNormalizedCode θ s m) (forcingNormalizedCode η z n) := by
  have hP (i : V) (hi : i ∈ θ) :
      (forcingNormalizationCarriers θ s m) ‘ i = (forcingNormalizationCarriers η z n) ‘ i := by
    rw [forcingNormalizationCarriers_value hi, forcingNormalizationCarriers_value (hθη i hi),
      hs.tableP.value_of_subset hz.tableP he.subP hi, hm i hi]
  apply ForcingCodeExtends.of_values hc hd hθη
  · simpa only [forcingNormalizedCode, forcingCodeP_code] using hP
  · intro i hi
    simp only [forcingNormalizedCode, forcingCodeR_code]
    rw [forcingNormalizationOrders_value hi, forcingNormalizationOrders_value (hθη i hi),
      hP i hi, hs.tableR.value_of_subset hz.tableR he.subR hi]
  · intro i hi j hj
    simp only [forcingNormalizedCode, forcingCodeπ_code]
    rw [forcingNormalizationProjections_value hi hj,
      forcingNormalizationProjections_value (hθη i hi) (hθη j hj), hP j hj,
      hs.tableπ.value_of_subset hz.tableπ he.subπ (kpair_mem_iff.mpr ⟨hi, hj⟩)]
  · intro i hi j hj
    simp only [forcingNormalizedCode, forcingCodeE_code]
    rw [forcingNormalizationSections_value hi hj,
      forcingNormalizationSections_value (hθη i hi) (hθη j hj), hP i hi,
      hs.tableE.value_of_subset hz.tableE he.subE (kpair_mem_iff.mpr ⟨hi, hj⟩)]
  · intro i hi j hj
    simp only [forcingNormalizedCode, forcingCodeL_code]
    rw [forcingNormalizationLifts_value hi hj,
      forcingNormalizationLifts_value (hθη i hi) (hθη j hj), hP i hi, hP j hj,
      hs.tableL.value_of_subset hz.tableL he.subL (kpair_mem_iff.mpr ⟨hi, hj⟩)]
  · intro i hi
    simpa only [forcingNormalizedCode, forcingCodet_code] using
      hs.tablet.value_of_subset hz.tablet he.subt hi

end ZFVP
