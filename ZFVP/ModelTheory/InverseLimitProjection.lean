import ZFVP.SetTheory.ForcingThreadSplice
import ZFVP.SetTheory.ForcingThreadMaps
import ZFVP.ModelTheory.ForcingProjection

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- Coherent coded lifts give exact inverse-limit projections without a choice hypothesis. -/
theorem forcingInverseLimit_coordinate_projection {θ P R π E L U i : V} [IsOrdinal θ]
    (h : IsSplitForcingSystem θ P π E) (hL : IsCoherentForcingLift θ P R π L)
    (hi : i ∈ θ) (hU : ∀ j ∈ θ, P ‘ j ⊆ U)
    (hπ : ∀ j ∈ i, ∀ p ∈ P ‘ i, ∀ q ∈ P ‘ i, ⟨p, q⟩ₖ ∈ R ‘ i →
      ⟨(π ‘ ⟨j, i⟩ₖ) ‘ p, (π ‘ ⟨j, i⟩ₖ) ‘ q⟩ₖ ∈ R ‘ j) :
    IsForcingProjection (P ‘ i) (R ‘ i) (forcingInverseLimit θ P π U)
      (forcingThreadOrder θ R (forcingInverseLimit θ P π U))
      (forcingThreadCoordinate (forcingInverseLimit θ P π U) i) := by
  refine ⟨forcingThreadCoordinate_maps hi, ?_, ?_⟩
  · intro f _hf g _hg hfg
    exact forcingThreadCoordinate_monotone hi hfg
  · intro f hf b hb hbf
    rw [forcingThreadCoordinate_value hf] at hbf
    have hg := forcingThreadSplice_mem h hL hf hi hb hbf hU
    refine ⟨forcingThreadSplice θ π L f i b, hg,
      forcingThreadSplice_le h hL hf hi hb hbf hU hπ, ?_⟩
    rw [forcingThreadCoordinate_value hg, forcingThreadSplice_value hi,
      forcingSpliceValue_self h hL hf hi hb hbf]

end ZFVP
