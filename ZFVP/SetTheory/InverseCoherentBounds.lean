import ZFVP.SetTheory.ForcingLimitBounds

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem inverse_coherentBoundColumn {θ P R π E B U i I : V} [IsOrdinal θ]
    (h : IsSplitForcingSystem θ P π E) (o : IsOrderedSplitForcingSystem θ P R π E)
    (m : IsFunctionalSplitForcingSystem θ P π E) (hB : IsCoherentForcingBound θ P R π B i I)
    (hi : i ∈ θ) (hU : ∀ j ∈ θ, P ‘ j ⊆ U) :
    IsCoherentForcingBoundColumn θ P R B (forcingInverseLimit θ P π U)
      (forcingThreadOrder θ R (forcingInverseLimit θ P π U))
      (forcingLimitProjectionColumn θ (forcingInverseLimit θ P π U))
      (forcingLimitBound θ P π B i I (forcingInverseLimit θ P π U)) i I := by
  have hpb {f p : V} (hf : IsForcingDirectedFamily (forcingInverseLimit θ P π U)
      (forcingThreadOrder θ R (forcingInverseLimit θ P π U)) I f)
      (hb : ∀ a ∈ I, ⟨p, ((forcingLimitProjectionColumn θ (forcingInverseLimit θ P π U)) ‘ i) ‘ (f ‘ a)⟩ₖ ∈ R ‘ i) :
      ∀ a ∈ I, ⟨p, (f ‘ a) ‘ i⟩ₖ ∈ R ‘ i := by
    intro a ha
    simpa only [forcingLimitProjectionColumn_value hi,
      forcingThreadCoordinate_value (function_value_mem hf.1 ha)] using hb a ha
  constructor
  · intro f hf p hp hb
    rw [forcingLimitBound_value hf.1 hp]
    have hq := forcingBoundThread_mem h o hB hi hf hp (hpb hf hb) m hU
    refine ⟨hq, ?_, ?_⟩
    · intro a ha
      apply (mem_forcingThreadOrder_iff _ _ _ _ _).mpr
      refine ⟨hq, function_value_mem hf.1 ha, fun j hj ↦ ?_⟩
      rw [forcingBoundThread_value hj]
      exact (forcingBoundValue_bound h o hB hi hf hp (hpb hf hb) hj).2 a ha
    · rw [forcingLimitProjectionColumn_value hi, forcingThreadCoordinate_value hq, forcingBoundThread_value hi]
      exact forcingBoundValue_self h hB hi hf hp (hpb hf hb)
  · intro j hj hij f hf p hp hb
    rw [forcingLimitBound_value hf.1 hp]
    have hq := forcingBoundThread_mem h o hB hi hf hp (hpb hf hb) m hU
    have hji : j ∉ i := fun hji ↦ mem_irrefl j (hij j hji)
    rw [forcingLimitProjectionColumn_value hj, forcingThreadCoordinate_value hq, forcingBoundThread_value hj,
      forcingCoordinateFamily_compose hf.1 hj]
    simp only [forcingBoundValue, ite_eq_right hji]

end ZFVP
