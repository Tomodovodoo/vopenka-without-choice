import ZFVP.ModelTheory.ForcingNormalizationLimits
import ZFVP.ModelTheory.ForcingNormalizationExtension

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem IsForcingNormalizationFamily.threadFamily {θ s m C A B : V} [IsOrdinal θ]
    (h : IsForcingNormalizationFamily θ s m) (hs : IsForcingIterationCode θ s) (h0 : ∅ ∈ θ)
    (hD : forcingDirectLimit θ (forcingCodeP s) (forcingCodeπ s) (forcingCodeE s) (forcingCodeUniverse s) ⊆ C)
    (hr : IsForcingRetraction A B C (forcingThreadOrder θ (forcingCodeR s) C) (forcingThreadActionMap θ m C))
    (hB : IsForcingPreorder A B)
    (he : ∀ f ∈ C,
      ⟨(forcingThreadActionMap θ m C) ‘ f, f⟩ₖ ∈ forcingThreadOrder θ (forcingCodeR s) C ∧
      ⟨f, (forcingThreadActionMap θ m C) ‘ f⟩ₖ ∈ forcingThreadOrder θ (forcingCodeR s) C) :
    IsForcingNormalizationFamily (succ θ) (forcingThreadCode θ s C)
      (forcingFamilyNext θ m (forcingThreadActionMap θ m C)) := by
  unfold forcingThreadCode
  apply h.extend hr hB he
  · have ht := hD _ (forcingSectionThread_mem hs.system.split h0
      (hs.system.tops.top ∅ h0).1 hs.subset_universe)
    rw [forcingThreadActionMap_value ht, h.thread_section h0 (hs.system.tops.top ∅ h0).1, h.fixesTop ∅ h0]
  · intro i hi f hf
    have hm := hr.inclusion _ (function_value_mem hr.maps hf)
    rw [forcingLimitProjectionColumn_value hi, forcingThreadCoordinate_value hm,
      forcingThreadCoordinate_value hf, forcingThreadActionMap_value hf, forcingThreadAction_value hi]
  · intro i hi p hp
    have hmp := (h.retraction i hi).inclusion _ (function_value_mem (h.retraction i hi).maps hp)
    have hsec := hD _ (forcingSectionThread_mem hs.system.split hi hp hs.subset_universe)
    rw [forcingLimitSectionColumn_value hi, forcingThreadSection_value hp,
      forcingThreadSection_value hmp, forcingThreadActionMap_value hsec, h.thread_section hi hp]

theorem forcingNormalizationDirect_family {θ s m : V} [IsOrdinal θ]
    (hs : IsForcingIterationCode θ s) (h : IsForcingNormalizationFamily θ s m) (h0 : ∅ ∈ θ) :
    IsForcingNormalizationFamily (succ θ) (forcingDirectCode θ s) (forcingNormalizationDirect θ s m) := by
  have hr := forcingNormalizationDirect_retraction hs h
  have ht := forcingThreadOrder_preorder hs.system.order.preorder
    (fun f (hf : f ∈ forcingDirectLimit θ (forcingNormalizationCarriers θ s m)
      (forcingCodeπ s) (forcingCodeE s) (forcingCodeUniverse s)) i hi ↦
      h.inclusion i hi _ (((mem_forcingInverseLimit_iff _ _ _ _ _).mp
        (forcingDirectLimit_subset _ _ _ _ _ _ hf)).2.1 i hi))
  have he (f : V) := forcingNormalizationDirect_equivalent hs h (f := f)
  simp only [forcingNormalizationDirectMap, forcingDirectCode, forcingThreadCode_poset,
    forcingThreadCode_order] at hr he
  simpa only [forcingNormalizationDirect, forcingNormalizationDirectMap, forcingDirectCode,
    forcingThreadCode_poset] using h.threadFamily hs h0 (subset_refl _) hr ht he

/-- This extends the family to the raw inverse code; the source collapse is a further step. -/
theorem forcingNormalizationInverse_family {θ s m : V} [IsOrdinal θ]
    (hs : IsForcingIterationCode θ s) (h : IsForcingNormalizationFamily θ s m) (h0 : ∅ ∈ θ) :
    IsForcingNormalizationFamily (succ θ) (forcingInverseCode θ s) (forcingNormalizationInverse θ s m) := by
  have hr := forcingNormalizationInverse_retraction hs h
  have ht := forcingThreadOrder_preorder hs.system.order.preorder
    (fun f (hf : f ∈ forcingInverseLimit θ (forcingNormalizationCarriers θ s m)
      (forcingCodeπ s) (forcingCodeUniverse s)) i hi ↦
      h.inclusion i hi _ (((mem_forcingInverseLimit_iff _ _ _ _ _).mp hf).2.1 i hi))
  have he (f : V) := forcingNormalizationInverse_equivalent hs h (f := f)
  simp only [forcingNormalizationInverseMap, forcingInverseCode, forcingThreadCode_poset,
    forcingThreadCode_order] at hr he
  simpa only [forcingNormalizationInverse, forcingNormalizationInverseMap, forcingInverseCode,
    forcingThreadCode_poset] using h.threadFamily hs h0 (forcingDirectLimit_subset _ _ _ _ _) hr ht
      he

end ZFVP
