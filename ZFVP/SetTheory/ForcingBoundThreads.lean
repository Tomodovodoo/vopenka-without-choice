import ZFVP.SetTheory.CoherentForcingBounds

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

private theorem subset_of_not_mem {i j : V} [IsOrdinal i] [IsOrdinal j] (hj : j ∉ i) : i ⊆ j := by
  rcases IsOrdinal.mem_trichotomy j i with hji | rfl | hij
  · exact (hj hji).elim
  · exact subset_refl _
  · exact IsOrdinal.toIsTransitive.transitive _ hij

variable {θ P R π E B U I f i p : V} [IsOrdinal θ]
  (h : IsSplitForcingSystem θ P π E) (o : IsOrderedSplitForcingSystem θ P R π E)
  (hB : IsCoherentForcingBound θ P R π B i I) (hi : i ∈ θ)
  (hf : IsForcingDirectedFamily (forcingInverseLimit θ P π U)
    (forcingThreadOrder θ R (forcingInverseLimit θ P π U)) I f)
  (hp : p ∈ P ‘ i) (hb : ∀ a ∈ I, ⟨p, (f ‘ a) ‘ i⟩ₖ ∈ R ‘ i)

include h hB hi hf hp hb

theorem forcingBoundValue_self : forcingBoundValue π B I f i p i = p := by
  have hh := hB.bound i hi (subset_refl _) _ (forcingCoordinateFamily_directed hf hi) p hp
    (forcingCoordinateFamily_below h hi hi (subset_refl _) hf.1 hb)
  rw [h.projId hi hh.1] at hh
  simpa only [forcingBoundValue, ite_eq_right (mem_irrefl i)] using hh.2.2

include o

theorem forcingBoundValue_bound {j : V} (hj : j ∈ θ) :
    forcingBoundValue π B I f i p j ∈ P ‘ j ∧
      ∀ a ∈ I, ⟨forcingBoundValue π B I f i p j, (f ‘ a) ‘ j⟩ₖ ∈ R ‘ j := by
  classical
  let := IsOrdinal.of_mem hi
  let := IsOrdinal.of_mem hj
  by_cases hji : j ∈ i
  · simp only [forcingBoundValue, ite_eq_left hji]
    have hji' := IsOrdinal.toIsTransitive.transitive _ hji
    refine ⟨h.projMaps j hj i hi hji' p hp, ?_⟩
    intro a ha
    have hfa := function_value_mem hf.1 ha
    have hfi := ((mem_forcingInverseLimit_iff _ _ _ _ _).mp hfa).2.1 i hi
    rw [← forcingInverseLimit_project_subset h hfa hj hi hji']
    exact o.projMono j hj i hi hji' p hp _ hfi (hb a ha)
  · have hij := subset_of_not_mem hji
    have hh := hB.bound j hj hij _ (forcingCoordinateFamily_directed hf hj) p hp
      (forcingCoordinateFamily_below h hi hj hij hf.1 hb)
    simp only [forcingBoundValue, ite_eq_right hji]
    refine ⟨hh.1, fun a ha ↦ ?_⟩
    simpa only [forcingCoordinateFamily_value ha] using hh.2.1 a ha

omit o in
 theorem forcingBoundValue_coherent (m : IsFunctionalSplitForcingSystem θ P π E)
    {j k : V} (hj : j ∈ θ) (hk : k ∈ θ) (hjk : j ∈ k) :
    (π ‘ ⟨j, k⟩ₖ) ‘ (forcingBoundValue π B I f i p k) = forcingBoundValue π B I f i p j := by
  classical
  let := IsOrdinal.of_mem hi
  let := IsOrdinal.of_mem hj
  let := IsOrdinal.of_mem hk
  have hjk' := IsOrdinal.toIsTransitive.transitive _ hjk
  by_cases hki : k ∈ i
  · have hji := IsOrdinal.toIsTransitive.mem_trans hjk hki
    simp only [forcingBoundValue, ite_eq_left hki, ite_eq_left hji]
    exact h.projComp j hj k hk i hi hjk' (IsOrdinal.toIsTransitive.transitive _ hki) p hp
  · have hik := subset_of_not_mem hki
    have hfk := forcingCoordinateFamily_directed hf hk
    have hpb := forcingCoordinateFamily_below h hi hk hik hf.1 hb
    have hh := hB.bound k hk hik _ hfk p hp hpb
    by_cases hji : j ∈ i
    · simp only [forcingBoundValue, ite_eq_right hki, ite_eq_left hji]
      rw [← h.projComp j hj i hi k hk (IsOrdinal.toIsTransitive.transitive _ hji) hik _ hh.1, hh.2.2]
    · have hij := subset_of_not_mem hji
      have hc := hB.commute j hj k hk hij hjk' _ hfk p hp hpb
      rw [forcingCoordinateFamily_project h hf.1 hj hk hjk' (m.projection j hj k hk hjk')] at hc
      simpa only [forcingBoundValue, ite_eq_right hki, ite_eq_right hji] using hc

theorem forcingBoundThread_mem (m : IsFunctionalSplitForcingSystem θ P π E)
    (hU : ∀ j ∈ θ, P ‘ j ⊆ U) :
    forcingBoundThread θ π B I f i p ∈ forcingInverseLimit θ P π U := by
  apply (mem_forcingInverseLimit_iff _ _ _ _ _).mpr
  refine ⟨definableGraph_mem_function_of_mapsTo _ _ _ _ (fun j hj ↦
    hU j hj _ (forcingBoundValue_bound h o hB hi hf hp hb hj).1), ?_, ?_⟩
  · intro j hj
    rw [forcingBoundThread_value hj]
    exact (forcingBoundValue_bound h o hB hi hf hp hb hj).1
  · intro k hk j hjk hj
    rw [forcingBoundThread_value hk, forcingBoundThread_value hj]
    exact forcingBoundValue_coherent h hB hi hf hp hb m hj hk hjk

omit hf hp hb in
 theorem forcingInverseLimit_relativeDirectedClosedAt
    (m : IsFunctionalSplitForcingSystem θ P π E) (hU : ∀ j ∈ θ, P ‘ j ⊆ U) :
    IsForcingRelativeDirectedClosedAt (P ‘ i) (R ‘ i) (forcingInverseLimit θ P π U)
      (forcingThreadOrder θ R (forcingInverseLimit θ P π U))
      (forcingThreadCoordinate (forcingInverseLimit θ P π U) i) I := by
  intro f hf p hp hb
  have hb' : ∀ a ∈ I, ⟨p, (f ‘ a) ‘ i⟩ₖ ∈ R ‘ i := by
    intro a ha
    simpa only [forcingThreadCoordinate_value (function_value_mem hf.1 ha)] using hb a ha
  have hq := forcingBoundThread_mem h o hB hi hf hp hb' m hU
  refine ⟨forcingBoundThread θ π B I f i p, hq, ?_, ?_⟩
  · intro a ha
    apply (mem_forcingThreadOrder_iff _ _ _ _ _).mpr
    refine ⟨hq, function_value_mem hf.1 ha, fun j hj ↦ ?_⟩
    rw [forcingBoundThread_value hj]
    exact (forcingBoundValue_bound h o hB hi hf hp hb' hj).2 a ha
  · rw [forcingThreadCoordinate_value hq, forcingBoundThread_value hi]
    exact forcingBoundValue_self h hB hi hf hp hb'

end ZFVP
