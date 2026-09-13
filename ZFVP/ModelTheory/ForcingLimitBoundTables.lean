import ZFVP.ModelTheory.ForcingInverseBoundTable
import ZFVP.ModelTheory.WoodinDirectIndex
import ZFVP.SetTheory.DirectCoherentBounds
import ZFVP.SetTheory.LimitBoundSections

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def forcingDirectBoundTable (θ s B i I : V) : V :=
  forcingFamilyNext θ B (forcingLimitBound θ (forcingCodeP s) (forcingCodeπ s) B i I
    (forcingDirectLimit θ (forcingCodeP s) (forcingCodeπ s) (forcingCodeE s) (forcingCodeUniverse s)))

theorem IsForcingIterationCode.direct_bound_table {θ s B i I : V} [IsOrdinal θ]
    (h : IsForcingIterationCode θ s) (hi : i ∈ θ) (hI : I ∈ internalCofinality θ)
    (hB : IsCoherentForcingBound θ (forcingCodeP s) (forcingCodeR s) (forcingCodeπ s) B i I)
    (hc : IsSectionCompatibleForcingBound θ (forcingCodeP s) (forcingCodeR s) (forcingCodeπ s)
      (forcingCodeE s) B i I) :
    IsCoherentForcingBound (succ θ) (forcingCodeP (forcingDirectCode θ s))
      (forcingCodeR (forcingDirectCode θ s)) (forcingCodeπ (forcingDirectCode θ s))
      (forcingDirectBoundTable θ s B i I) i I := by
  have hcol := direct_coherentBoundColumn h.system.split h.system.order h.system.functions hB hc hi hI h.subset_universe
  have he := hB.extend hcol hi
  simpa only [forcingDirectCode, forcingThreadCode, forcingIterationCodeNext,
    forcingCodeP_code, forcingCodeR_code, forcingCodeπ_code, forcingDirectBoundTable] using he

theorem IsForcingIterationCode.inverse_bound_table_sectionCompatible {θ s B i I : V} [IsOrdinal θ]
    (h : IsForcingIterationCode θ s) (hi : i ∈ θ)
    (hB : IsCoherentForcingBound θ (forcingCodeP s) (forcingCodeR s) (forcingCodeπ s) B i I)
    (hc : IsSectionCompatibleForcingBound θ (forcingCodeP s) (forcingCodeR s) (forcingCodeπ s)
      (forcingCodeE s) B i I) :
    IsSectionCompatibleForcingBound (succ θ) (forcingCodeP (forcingInverseCode θ s))
      (forcingCodeR (forcingInverseCode θ s)) (forcingCodeπ (forcingInverseCode θ s))
      (forcingCodeE (forcingInverseCode θ s)) (forcingInverseBoundTable θ s B i I) i I := by
  have hcol := inverse_coherentBoundColumn h.system.split h.system.order h.system.functions hB hi h.subset_universe
  have hs := limit_sectionCompatibleBoundColumn h.system.split h.system.functions hB hc hi
    h.subset_universe (forcingDirectLimit_subset _ _ _ _ _)
  have he := hc.extend hcol hs hi
  simpa only [forcingInverseCode, forcingThreadCode, forcingIterationCodeNext,
    forcingCodeP_code, forcingCodeR_code, forcingCodeπ_code, forcingCodeE_code, forcingInverseBoundTable] using he

theorem IsForcingIterationCode.direct_bound_table_sectionCompatible {θ s B i I : V} [IsOrdinal θ]
    (h : IsForcingIterationCode θ s) (hi : i ∈ θ) (hI : I ∈ internalCofinality θ)
    (hB : IsCoherentForcingBound θ (forcingCodeP s) (forcingCodeR s) (forcingCodeπ s) B i I)
    (hc : IsSectionCompatibleForcingBound θ (forcingCodeP s) (forcingCodeR s) (forcingCodeπ s)
      (forcingCodeE s) B i I) :
    IsSectionCompatibleForcingBound (succ θ) (forcingCodeP (forcingDirectCode θ s))
      (forcingCodeR (forcingDirectCode θ s)) (forcingCodeπ (forcingDirectCode θ s))
      (forcingCodeE (forcingDirectCode θ s)) (forcingDirectBoundTable θ s B i I) i I := by
  have hcol := direct_coherentBoundColumn h.system.split h.system.order h.system.functions hB hc hi hI h.subset_universe
  have hs := limit_sectionCompatibleBoundColumn h.system.split h.system.functions hB hc hi
    h.subset_universe (subset_refl _)
  have he := hc.extend hcol hs hi
  simpa only [forcingDirectCode, forcingThreadCode, forcingIterationCodeNext,
    forcingCodeP_code, forcingCodeR_code, forcingCodeπ_code, forcingCodeE_code, forcingDirectBoundTable] using he

theorem IsWoodinIteration.direct_bound_table {δ θ s K B i I : V} [IsOrdinal θ]
    (h : IsWoodinIteration δ θ s K) (hlim : ∀ j ∈ θ, succ j ∈ θ)
    (hinac : IsChoicelessInaccessible (woodinLimitCardinal K)) (hi : i ∈ θ) (hI : I ∈ K ‘ i)
    (hB : IsCoherentForcingBound θ (forcingCodeP s) (forcingCodeR s) (forcingCodeπ s) B i I)
    (hc : IsSectionCompatibleForcingBound θ (forcingCodeP s) (forcingCodeR s) (forcingCodeπ s)
      (forcingCodeE s) B i I) :
    IsCoherentForcingBound (succ θ) (forcingCodeP (forcingDirectCode θ s))
      (forcingCodeR (forcingDirectCode θ s)) (forcingCodeπ (forcingDirectCode θ s))
      (forcingDirectBoundTable θ s B i I) i I :=
  h.code.direct_bound_table hi (h.short_below_direct_cofinality hlim hinac hi hI) hB hc

end ZFVP
