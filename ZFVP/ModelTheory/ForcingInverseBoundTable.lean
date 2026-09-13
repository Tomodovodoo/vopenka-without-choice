import ZFVP.SetTheory.InverseCoherentBounds
import ZFVP.ModelTheory.ForcingLimitCode

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def forcingInverseBoundTable (θ s B i I : V) : V :=
  forcingFamilyNext θ B (forcingLimitBound θ (forcingCodeP s) (forcingCodeπ s) B i I
    (forcingInverseLimit θ (forcingCodeP s) (forcingCodeπ s) (forcingCodeUniverse s)))

theorem IsForcingIterationCode.inverse_bound_table {θ s B i I : V} [IsOrdinal θ]
    (h : IsForcingIterationCode θ s) (hi : i ∈ θ)
    (hB : IsCoherentForcingBound θ (forcingCodeP s) (forcingCodeR s) (forcingCodeπ s) B i I) :
    IsCoherentForcingBound (succ θ) (forcingCodeP (forcingInverseCode θ s))
      (forcingCodeR (forcingInverseCode θ s)) (forcingCodeπ (forcingInverseCode θ s))
      (forcingInverseBoundTable θ s B i I) i I := by
  have hc := inverse_coherentBoundColumn h.system.split h.system.order h.system.functions hB hi h.subset_universe
  have he := hB.extend hc hi
  simpa only [forcingInverseCode, forcingThreadCode, forcingIterationCodeNext,
    forcingCodeP_code, forcingCodeR_code, forcingCodeπ_code, forcingInverseBoundTable] using he

theorem IsForcingIterationCode.inverse_relativeDirectedClosedAt {θ s B i I : V} [IsOrdinal θ]
    (h : IsForcingIterationCode θ s) (hi : i ∈ θ)
    (hB : IsCoherentForcingBound θ (forcingCodeP s) (forcingCodeR s) (forcingCodeπ s) B i I) :
    IsForcingRelativeDirectedClosedAt ((forcingCodeP s) ‘ i) ((forcingCodeR s) ‘ i)
      ((forcingCodeP (forcingInverseCode θ s)) ‘ θ) ((forcingCodeR (forcingInverseCode θ s)) ‘ θ)
      ((forcingCodeπ (forcingInverseCode θ s)) ‘ ⟨i, θ⟩ₖ) I := by
  have hh := forcingInverseLimit_relativeDirectedClosedAt h.system.split h.system.order hB hi
    h.system.functions h.subset_universe
  simpa only [forcingInverseCode, forcingThreadCode, forcingIterationCodeNext,
    forcingCodeP_code, forcingCodeR_code, forcingCodeπ_code, forcingFamilyNext_new,
    forcingMatrixNext_column hi, forcingLimitProjectionColumn_value hi] using hh

end ZFVP
