import ZFVP.ModelTheory.ForcingNormalizationLiftClosure
import ZFVP.ModelTheory.ForcingNormalizationLimitFamily

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem forcingThreadActionMap_fixed_coordinates {θ s m C f : V}
    (h : IsForcingNormalizationFamily θ s m)
    (hC : C ⊆ forcingInverseLimit θ (forcingCodeP s) (forcingCodeπ s) (forcingCodeUniverse s)) :
    f ∈ forcingMapFixedPoints C (forcingThreadActionMap θ m C) ↔
      f ∈ C ∧ ∀ i ∈ θ, f ‘ i ∈ (forcingNormalizationCarriers θ s m) ‘ i := by
  constructor
  · intro hf
    have hf' := mem_sep_iff.mp hf
    refine ⟨hf'.1, ?_⟩
    intro i hi
    rw [forcingNormalizationCarriers_value hi]
    refine mem_sep_iff.mpr ⟨((mem_forcingInverseLimit_iff _ _ _ _ _).mp (hC f hf'.1)).2.1 i hi, ?_⟩
    have he := congrArg (fun g : V ↦ g ‘ i) hf'.2
    rwa [forcingThreadActionMap_value hf'.1, forcingThreadAction_value hi] at he
  · rintro ⟨hf, hv⟩
    apply mem_sep_iff.mpr
    refine ⟨hf, ?_⟩
    rw [forcingThreadActionMap_value hf]
    exact forcingThreadAction_fixes ((mem_forcingInverseLimit_iff _ _ _ _ _).mp (hC f hf)).1 hv h.fixes

theorem IsForcingNormalizationLiftClosed.splice_coordinates {θ s m f i b : V} [IsOrdinal θ]
    (hL : IsForcingNormalizationLiftClosed θ s m)
    (h : IsForcingNormalizationFamily θ s m) (hs : IsForcingIterationCode θ s)
    (hf : f ∈ forcingInverseLimit θ (forcingCodeP s) (forcingCodeπ s) (forcingCodeUniverse s))
    (hv : ∀ j ∈ θ, f ‘ j ∈ (forcingNormalizationCarriers θ s m) ‘ j)
    (hi : i ∈ θ) (hb : b ∈ (forcingNormalizationCarriers θ s m) ‘ i)
    (hle : ⟨b, f ‘ i⟩ₖ ∈ (forcingCodeR s) ‘ i) :
    ∀ j ∈ θ, (forcingThreadSplice θ (forcingCodeπ s) (forcingCodeL s) f i b) ‘ j ∈
      (forcingNormalizationCarriers θ s m) ‘ j := by
  intro j hj
  let := IsOrdinal.of_mem hi
  let := IsOrdinal.of_mem hj
  rw [forcingThreadSplice_value hj]
  classical
  by_cases hji : j ∈ i
  · simp only [forcingSpliceValue, ite_eq_left hji]
    exact h.projection_mem hs hj hi (IsOrdinal.toIsTransitive.transitive _ hji) hb
  · have hij : i ⊆ j := by
      rcases IsOrdinal.mem_trichotomy j i with hji' | rfl | hij
      · exact (hji hji').elim
      · exact subset_refl _
      · exact IsOrdinal.toIsTransitive.transitive _ hij
    simp only [forcingSpliceValue, ite_eq_right hji]
    apply hL i hi j hj hij _ (hv j hj) b hb
    rwa [forcingInverseLimit_project_subset hs.system.split hf hi hj hij]

theorem IsForcingNormalizationLiftClosed.thread {θ s m C : V} [IsOrdinal θ]
    (hL : IsForcingNormalizationLiftClosed θ s m)
    (h : IsForcingNormalizationFamily θ s m) (hs : IsForcingIterationCode θ s)
    (hC : C ⊆ forcingInverseLimit θ (forcingCodeP s) (forcingCodeπ s) (forcingCodeUniverse s))
    (hc : IsCoherentForcingLiftColumn θ (forcingCodeP s) (forcingCodeR s) (forcingCodeπ s)
      (forcingCodeL s) C (forcingThreadOrder θ (forcingCodeR s) C)
      (forcingLimitProjectionColumn θ C)
      (forcingLimitLiftColumn C θ (forcingCodeP s) (forcingCodeπ s) (forcingCodeL s))) :
    IsForcingNormalizationLiftClosed (succ θ) (forcingThreadCode θ s C)
      (forcingFamilyNext θ m (forcingThreadActionMap θ m C)) := by
  unfold forcingThreadCode
  apply hL.extend
  intro i hi a ha b hb hle
  have ha' := (forcingThreadActionMap_fixed_coordinates h hC).mp ha
  have hbP := h.inclusion i hi b hb
  have hlC := (hc.lift i hi a ha'.1 b hbP hle).1
  rw [forcingLimitProjectionColumn_value hi, forcingThreadCoordinate_value ha'.1] at hle
  rw [forcingLimitLiftColumn_value hi, forcingLimitLift_value ha'.1 hbP] at hlC ⊢
  exact (forcingThreadActionMap_fixed_coordinates h hC).mpr
    ⟨hlC, hL.splice_coordinates h hs (hC a ha'.1) ha'.2 hi hb hle⟩

theorem IsForcingNormalizationLiftClosed.inverse_splice {θ s m f i b : V} [IsOrdinal θ]
    (hL : IsForcingNormalizationLiftClosed θ s m)
    (h : IsForcingNormalizationFamily θ s m) (hs : IsForcingIterationCode θ s)
    (hf : f ∈ forcingMapFixedPoints
      (forcingInverseLimit θ (forcingCodeP s) (forcingCodeπ s) (forcingCodeUniverse s))
      (forcingThreadActionMap θ m
        (forcingInverseLimit θ (forcingCodeP s) (forcingCodeπ s) (forcingCodeUniverse s))))
    (hi : i ∈ θ) (hb : b ∈ (forcingNormalizationCarriers θ s m) ‘ i)
    (hle : ⟨b, f ‘ i⟩ₖ ∈ (forcingCodeR s) ‘ i) :
    forcingThreadSplice θ (forcingCodeπ s) (forcingCodeL s) f i b ∈ forcingMapFixedPoints
      (forcingInverseLimit θ (forcingCodeP s) (forcingCodeπ s) (forcingCodeUniverse s))
      (forcingThreadActionMap θ m
        (forcingInverseLimit θ (forcingCodeP s) (forcingCodeπ s) (forcingCodeUniverse s))) := by
  have hf' := (forcingThreadActionMap_fixed_coordinates h (subset_refl _)).mp hf
  apply (forcingThreadActionMap_fixed_coordinates h (subset_refl _)).mpr
  exact ⟨forcingThreadSplice_mem hs.system.split hs.system.lifts hf'.1 hi
    (h.inclusion i hi b hb) hle hs.subset_universe,
    hL.splice_coordinates h hs hf'.1 hf'.2 hi hb hle⟩

theorem forcingNormalizationDirect_liftClosed {θ s m : V} [IsOrdinal θ]
    (hs : IsForcingIterationCode θ s) (h : IsForcingNormalizationFamily θ s m)
    (hL : IsForcingNormalizationLiftClosed θ s m) (h0 : ∅ ∈ θ) :
    IsForcingNormalizationLiftClosed (succ θ) (forcingDirectCode θ s) (forcingNormalizationDirect θ s m) := by
  simpa only [forcingNormalizationDirect, forcingNormalizationDirectMap, forcingDirectCode,
    forcingThreadCode_poset] using hL.thread h hs (forcingDirectLimit_subset _ _ _ _ _)
      (hs.system.directColumn h0 hs.subset_universe).lifts

theorem forcingNormalizationInverse_liftClosed {θ s m : V} [IsOrdinal θ]
    (hs : IsForcingIterationCode θ s) (h : IsForcingNormalizationFamily θ s m)
    (hL : IsForcingNormalizationLiftClosed θ s m) (h0 : ∅ ∈ θ) :
    IsForcingNormalizationLiftClosed (succ θ) (forcingInverseCode θ s) (forcingNormalizationInverse θ s m) := by
  simpa only [forcingNormalizationInverse, forcingNormalizationInverseMap, forcingInverseCode,
    forcingThreadCode_poset] using hL.thread h hs (subset_refl _)
      (hs.system.inverseColumn h0 hs.subset_universe).lifts

end ZFVP
