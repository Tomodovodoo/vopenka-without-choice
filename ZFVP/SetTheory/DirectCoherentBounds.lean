import ZFVP.SetTheory.DirectBoundThreads
import ZFVP.SetTheory.ForcingLimitBounds

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem forcingThreadDirectedFamily_mono {θ R C D I f : V} (h : C ⊆ D)
    (hf : IsForcingDirectedFamily C (forcingThreadOrder θ R C) I f) :
    IsForcingDirectedFamily D (forcingThreadOrder θ R D) I f := by
  refine ⟨mem_function_of_mem_function_of_subset hf.1 h, ?_⟩
  intro a ha b hb
  obtain ⟨c, hc, hca, hcb⟩ := hf.2 a ha b hb
  refine ⟨c, hc, ?_, ?_⟩
  · obtain ⟨hc', ha', he⟩ := (mem_forcingThreadOrder_iff _ _ _ _ _).mp hca
    exact (mem_forcingThreadOrder_iff _ _ _ _ _).mpr ⟨h _ hc', h _ ha', he⟩
  · obtain ⟨hc', hb', he⟩ := (mem_forcingThreadOrder_iff _ _ _ _ _).mp hcb
    exact (mem_forcingThreadOrder_iff _ _ _ _ _).mpr ⟨h _ hc', h _ hb', he⟩

theorem forcingCoordinateFamily_compose_subcarrier {θ P π U C I f j : V}
    (hC : C ⊆ forcingInverseLimit θ P π U) (hf : f ∈ C ^ I) (hj : j ∈ θ) :
    compose f (forcingThreadCoordinate C j) = forcingCoordinateFamily I f j := by
  have hm : forcingThreadCoordinate C j ∈ (P ‘ j) ^ C :=
    definableGraph_mem_function_of_mapsTo _ _ _ _ (fun g hg ↦
      ((mem_forcingInverseLimit_iff _ _ _ _ _).mp (hC g hg)).2.1 j hj)
  have hc := compose_function hf hm
  have hjf := forcingCoordinateFamily_mem (mem_function_of_mem_function_of_subset hf hC) hj
  let := IsFunction.of_mem hc
  let := IsFunction.of_mem hjf
  apply functions_eq_of_domain_values
  · rw [domain_eq_of_mem_function hc, domain_eq_of_mem_function hjf]
  · intro a ha
    rw [domain_eq_of_mem_function hc] at ha
    rw [value_compose_of_mem_function hf hm ha, forcingThreadCoordinate_value (function_value_mem hf ha),
      forcingCoordinateFamily_value ha]

theorem direct_coherentBoundColumn {θ P R π E B U i I : V} [IsOrdinal θ]
    (h : IsSplitForcingSystem θ P π E) (o : IsOrderedSplitForcingSystem θ P R π E)
    (m : IsFunctionalSplitForcingSystem θ P π E) (hB : IsCoherentForcingBound θ P R π B i I)
    (hc : IsSectionCompatibleForcingBound θ P R π E B i I)
    (hi : i ∈ θ) (hI : I ∈ internalCofinality θ) (hU : ∀ j ∈ θ, P ‘ j ⊆ U) :
    IsCoherentForcingBoundColumn θ P R B (forcingDirectLimit θ P π E U)
      (forcingThreadOrder θ R (forcingDirectLimit θ P π E U))
      (forcingLimitProjectionColumn θ (forcingDirectLimit θ P π E U))
      (forcingLimitBound θ P π B i I (forcingDirectLimit θ P π E U)) i I := by
  have hpb {f p : V} (hf : IsForcingDirectedFamily (forcingDirectLimit θ P π E U)
      (forcingThreadOrder θ R (forcingDirectLimit θ P π E U)) I f)
      (hb : ∀ a ∈ I, ⟨p, ((forcingLimitProjectionColumn θ (forcingDirectLimit θ P π E U)) ‘ i) ‘ (f ‘ a)⟩ₖ ∈ R ‘ i) :
      ∀ a ∈ I, ⟨p, (f ‘ a) ‘ i⟩ₖ ∈ R ‘ i := by
    intro a ha
    simpa only [forcingLimitProjectionColumn_value hi,
      forcingThreadCoordinate_value (function_value_mem hf.1 ha)] using hb a ha
  constructor
  · intro f hf p hp hb
    rw [forcingLimitBound_value hf.1 hp]
    have hq := forcingBoundThread_mem_direct h m hB hc hi hI hU hf hp (hpb hf hb)
    have hfi := forcingThreadDirectedFamily_mono (forcingDirectLimit_subset _ _ _ _ _) hf
    refine ⟨hq, ?_, ?_⟩
    · intro a ha
      apply (mem_forcingThreadOrder_iff _ _ _ _ _).mpr
      refine ⟨hq, function_value_mem hf.1 ha, fun j hj ↦ ?_⟩
      rw [forcingBoundThread_value hj]
      exact (forcingBoundValue_bound h o hB hi hfi hp (hpb hf hb) hj).2 a ha
    · rw [forcingLimitProjectionColumn_value hi, forcingThreadCoordinate_value hq, forcingBoundThread_value hi]
      exact forcingBoundValue_self h hB hi hfi hp (hpb hf hb)
  · intro j hj hij f hf p hp hb
    rw [forcingLimitBound_value hf.1 hp]
    have hq := forcingBoundThread_mem_direct h m hB hc hi hI hU hf hp (hpb hf hb)
    have hji : j ∉ i := fun hji ↦ mem_irrefl j (hij j hji)
    rw [forcingLimitProjectionColumn_value hj, forcingThreadCoordinate_value hq, forcingBoundThread_value hj,
      forcingCoordinateFamily_compose_subcarrier (forcingDirectLimit_subset _ _ _ _ _) hf.1 hj]
    simp only [forcingBoundValue, ite_eq_right hji]

end ZFVP
